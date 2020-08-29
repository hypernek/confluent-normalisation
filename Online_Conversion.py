#!/usr/bin/env python
# coding: utf-8

# In[4]:


from sage.combinat.finite_state_machine import *
import bisect

def check_confluent(coeffs):
    a = coeffs[0]
    b = coeffs[len(coeffs)-1]
    if b > a or b < 1:
        return False
    for i in range(len(coeffs)-1):
        if coeffs[i] != a:
            return False
    return True


def basis_polynomial(fieldgen, Basis_coeffs):
    m = len(Basis_coeffs) # basis order
    M = 0 
    for i in range (m):
        M -= Basis_coeffs[m-i-1]*fieldgen**i
    M += fieldgen**m
    return M

def init_field(q): 
    # initialize polynomial quotient ring
    R = PolynomialRing(IntegerRing(), 'y')
    y = R.gen()
    S = R.quotient(q, 'x')
    x = S.gen()
    return S

# calculate delay of converter
def get_converter_delta(basisBeta, inputAlphC, canonicalAlphA, verbose):
    delta = 0
    LHS = basisBeta + inputAlphC/(basisBeta)**delta
    while LHS > canonicalAlphA + 1:
        if(verbose):
            print(f'delta = {delta} : beta + c/beta**delta = {LHS} > {canonicalAlphA  + 1} = a + 1')
        delta += 1
        LHS = basisBeta + inputAlphC/(basisBeta)**delta
    if(verbose):
        print(f'delta = {delta} : beta + c/beta**delta = {LHS} <= {canonicalAlphA + 1} = a + 1')
    return delta

#calculate needed zeros    
def get_converter_k(basisBeta, inputAlphC, verbose):
    k = 0
    LHS = inputAlphC/(basisBeta-1)
    while LHS > basisBeta**k:
        if(verbose):
            print(f'k = {k} : {LHS} > {basisBeta**k} = beta**k')
        k += 1
    if(verbose):
        print(f'k = {k} : {LHS} <= {basisBeta**k} = beta**k')
    return k


def find_index_of_first_element_bigger_than(number,inlist):
    # using enumerate() + next() to find index of 
    # first element just greater than number
    return bisect.bisect_right(inlist, number)


class OnlineConverter:
    
    # class wrapper around transducer
    # keeps track of basis, basis sequence, delta, k, etc.
    ready = False
    
    # FUNCTIONS FOR SEQUENCE
    def generate_basis_sequence_toindex(self, toIndex,verbose=True):
        for i in range(len(self.Basis_Sequence),toIndex+1): # add new elements only if needed
            B_i = 0
            if (i < self.Basis_order):
                for j in range(i):
                    B_i += self.Basis_coeffs[j]*self.Basis_Sequence[i-j-1]
                B_i += 1
            else:
                for j in range(self.Basis_order):
                    B_i += self.Basis_coeffs[j]*self.Basis_Sequence[i-j-1]
            if(verbose):
                print(f'added basis element {B_i}')
            self.Basis_Sequence.append(B_i)

    def generate_basis_sequence_tovalue(self,toValue,verbose=True):
        # add new elements only if the number is really bigger
        if(toValue < self.Basis_Sequence[len(self.Basis_Sequence) - 1]): 
            return
        else:
            maxIndex = len(self.Basis_Sequence) - 1
        while toValue > self.Basis_Sequence[maxIndex]: 
            B_i = 0
            maxIndex += 1
            if (maxIndex < self.Basis_order):
                for j in range(maxIndex):
                    B_i += self.Basis_coeffs[j]*self.Basis_Sequence[maxIndex-j-1]
                B_i += 1
            else:
                for j in range(self.Basis_order):
                    B_i += self.Basis_coeffs[j]*self.Basis_Sequence[maxIndex-j-1]
            if(verbose):
                print(f'added basis element {B_i}')
            self.Basis_Sequence.append(B_i)

    def representation_value(self,representation):
        N = len(representation)
        self.generate_basis_sequence_toindex(N - 1)
        value = 0
        for i in range(N):
            value += self.Basis_Sequence[i]*representation[N - i - 1]
        return value


    # generate a greedy representation (least significant digit on the left)
    def greedy_representation(self,Number):
        if Number == 0:
            return [0]
        # generate more basis elements if needed
        self.generate_basis_sequence_tovalue(Number) 
        # find index of largest element of basis smaller than Number
        i = find_index_of_first_element_bigger_than(Number,self.Basis_Sequence) - 1
        representation = []
        Res = Number
        # greedy algorithm
        while (i >= 0):
            representation.append(Res//self.Basis_Sequence[i])
            Res = Res%self.Basis_Sequence[i]
            i = i - 1
        return representation

    def b_representation(self,Number, length, a):
        # create representation of a given length on alphabet {0,1,...,a}, if possible
        self.generate_basis_sequence_toindex(length)
        if (Number < self.Basis_Sequence[length]):
            representation = self.greedy_representation(Number)
            # add zeros to reach desired length
            while len(representation) < length:
                representation.insert(0,0)
            return representation
        else:
            print(f'\nMaking B-representation of number {Number} of size {length} on alphabet {self.A}')
            max_representable = 0
            for i in range(length):
                max_representable += a*self.Basis_Sequence[i]
            print(f'max representable value: {max_representable}')
            if(Number <= max_representable):
                representation = []
                for i in range(length):
                    a_i = min(a, Number // self.Basis_Sequence[length-i-1])
                    representation.append(a_i)
                    Number = Number - a_i * self.Basis_Sequence[length-i-1]
                print(f'Representation: {representation}')
                return representation
            else:
                raise Exception(f'number too big for given length! Number = {Number} > {max_representable} = a* Sum(B_j)' ) 
  
    # convert polynomial representation of a concrete converter state q(X)
    # to B-representation that will be its terminal function
    # for q \in \Z[X] returns the B-representation of \pi(q), if possible, greedy
    def terminal_function(self, state_polynomial):
        state_value = 0
        coeffs = state_polynomial.list() 
        # do not call coefficients() here, that returns a sparse coefficient list
        # example: q =-x**2 + 4*x, q.list() = [0,4,-1] but q.coefficients() = [4,-1]
        for i in range(len(coeffs)):
            state_value += coeffs[i]*self.Basis_Sequence[i] # polynomial coeffs are thankfully ordered by power
        representation = self.b_representation(state_value, self.delta, self.a)
        return representation

    def add_transient_successors(self, root_state, index_in_input, verbose):
        if(index_in_input < self.delta):
            index_in_input += 1
            for c_j in self.C:
                label = 'Invalid'
                nextpolylabel = root_state.label()[1] * self.x + c_j
                if index_in_input < self.delta:
                    label = (f'q_{index_in_input}', nextpolylabel)
                else:
                    label = nextpolylabel
                q_t = FSMState(label, is_final = True, color = index_in_input)
                self._onlineconverter.add_state(q_t)
                q_t.final_word_out = self.terminal_function(lift(nextpolylabel)) # lift converts quotient class to polynomial
                # add new c_j /epsilon transition ending in this state
                trans = FSMTransition(root_state,q_t,c_j ,None)
                self._onlineconverter.add_transition(trans)
                if(verbose):
                    print(f'Added state {q_t} with transition {trans}')
                # recursively add next states
                self.add_transient_successors(q_t, index_in_input, verbose) 
        else:
            return
    
    # constructor constructs converter right away
    def __init__(self, Basis_coeffs, c, verbose):
        self.Basis_coeffs = Basis_coeffs

        if(verbose):
            print(f'Initializing basis with coefficients {Basis_coeffs}')
            print('Reccurence: B_n = ', end='')
            for i in range(len(Basis_coeffs)):
                print(f'{Basis_coeffs[i]:+}B_n-{i} ', end='')
            print( '\n')

        print( 'Basis is confluent: ', check_confluent(Basis_coeffs))

        if(not(check_confluent(Basis_coeffs))):
            print('Basis not confluent, aborting')
            return

        self.Basis_order = len(Basis_coeffs)
        y = PolynomialRing(IntegerRing(), 'y').gen()
        z = PolynomialRing(AlgebraicField(), 'z').gen()

        M = basis_polynomial(y, Basis_coeffs)
        MR = basis_polynomial(z, Basis_coeffs)

        print(f'basis polynomial: {M}')

        # find the Pisot root
        self.beta = 1
        for root in MR.roots():
            if root[0] > self.beta:
                self.beta = root[0]
        print(f'beta = {self.beta}\n')

        # prepare alphabets
        a = Basis_coeffs[0]
        self.a = a
        self.c = c
        self.C = list(range(c+1))
        self.A = list(range(a+1))

        print(f'Input alphabet: {self.C} \nCanonical alphabet: {self.A}\n')
        print('Starting construction of on-line converter...')

        self.delta = get_converter_delta(self.beta, c, a, verbose)
        self.k = get_converter_k(self.beta, c, verbose)

        print(f'delay: delta = {self.delta}\ninput extra zeros: k = {self.k}\n')

        StateField = init_field(M)
        if(verbose):
            print(f'Prepared the ring {StateField}')

        self.Basis_Sequence = [1]
        # generate first delta members of basis sequence 
        self.generate_basis_sequence_toindex(self.delta, verbose)
        if(verbose):
            print(f'Members of basis sequence up to index delta = {self.delta} : {self.Basis_Sequence}')
            num = 13
            print(f'Greedy representation of {num} : {self.greedy_representation(num)}')
            print(f'value of {self.greedy_representation(num)} : = {self.representation_value(self.greedy_representation(num))}')

        # prepare for polynomial quotient ring
        x = StateField.gen()
        self.x = x
        
        # start On-Line Converter generation 
        # this is the underlying transducer 
        self._onlineconverter = Transducer( input_alphabet = self.C, output_alphabet = self.A)

        print('Generating transient states...')

        q_0 = FSMState((f'q_0',0*x + 0), is_initial = True, is_final = True, final_word_out = [], color = 0)
        self._onlineconverter.add_state(q_0)

        # states for initial k-1 zeros
        terminal_word = []
        for i in range(1,self.k):
            terminal_word.append(0) # build terminal word
            # create new transient state
            q_t = FSMState((f'q_{i}',0*x + 0), is_final = True, final_word_out = terminal_word, color = i)
            self._onlineconverter.add_state(q_t)
            # connect to preceeding state
            trans = FSMTransition((f'q_{i-1}',0*x + 0),q_t,0,None) # add new 0/epsilon transition ending in this state
            self._onlineconverter.add_transition(trans)
            if(verbose):
                print(f'Added state {q_t} with {trans}')

        # branching starts from a transient state
        if(self.k < self.delta): 
            # state where branching begins
            terminal_word.append(0) # build terminal word
            q_t_branch = FSMState((f'q_{self.k}',0*x + 0), is_final = True, final_word_out = terminal_word, color = self.k)
            self._onlineconverter.add_state(q_t_branch)
            # connect to preceeding state
            trans = FSMTransition((f'q_{self.k-1}',0*x + 0),q_t_branch,0,None) # add new 0/epsilon transition ending in this state
            self._onlineconverter.add_transition(trans)
            if(verbose):
                print(f'Added state {q_t_branch} with {trans}')
                print(f'States for initial {self.k} zeros done')
                # state where branching begins
                print(f'Starting branching from state {q_t_branch}: ')
            # subsequent branching is done recursively
            self.add_transient_successors(q_t_branch, self.k, verbose)      

        elif (self.k == self.delta):
            terminal_word.append(0) # build terminal word
            # create first synchronous state
            q_s = FSMState(0*x + 0, is_final = True, final_word_out = terminal_word, color = self.delta)
            self._onlineconverter.add_state(q_s)
            # connect to preceeding state
            trans = FSMTransition(f'q_{i-1}',q_s,0,None) # add new 0/epsilon transition ending in this state
            self._onlineconverter.add_transition(trans)
            if(verbose):
                print(f'Added state {q_s} with {trans}')
        else:
            print("K > DELTA???")

        print('Transient states done.\n')
        print('Generating synchronous states... ')

        #get initial synchronous states
        unprocessed_states = list(filter(lambda q : q.color == self.delta, self._onlineconverter.states()) )
        processed_states = []
        if(verbose):
            print(f'Initial synchronous states: {unprocessed_states}')
            print(f'Processed synchronous states: {processed_states}')

        def process_synchronous_state(q_s):
            nonlocal verbose, processed_states, unprocessed_states
            if(q_s in processed_states):
                if(verbose):
                    print(f'State {q_s} already processed')
                return
            else:
                if(verbose):
                    print(f'Processing state {q_s}:')
                for c_j in self.C:
                    # compute next state label
                    next_state_label = q_s.label()*self.x + c_j
                    # floor (q(beta)/q(beta)) evaluates to floor(1.00000000...)
                    # which raises "ValueError: cannot compute floor(1.000000000000000?) 
                    # using 512 bits of precision"
                    # so that's the reason for this
                    a_out = lift(next_state_label)(self.beta)/(self.beta)**self.delta            
                    for a_j in self.A:
                        if (a_out == a_j):
                            a_out = a_j;
                    a_out = floor(a_out)
                    next_state_label -= a_out*(self.x**self.delta)
                    if(next_state_label in map(FSMState.label, self._onlineconverter.states())):
                        if(verbose):
                            print(f'- {c_j}: Connecting to existing state {next_state_label}')
                        q_s_next = self._onlineconverter.state(next_state_label)
                    else:
                        # construct the new state and add it
                        q_s_next = FSMState(next_state_label,                                       is_final = True,                                       final_word_out = self.terminal_function(lift(next_state_label)),                                       color = self.delta)
                        self._onlineconverter.add_state(q_s_next)
                        unprocessed_states.append(q_s_next)
                        if(verbose):
                            print(f'- {c_j}: Added new state {q_s_next}')
                    # add new c_j|a_j transition going to this new state
                    trans = FSMTransition(q_s, q_s_next, c_j, a_out)
                    self._onlineconverter.add_transition(trans)
                    if(verbose):
                        print(f'-- Added {trans}')

                processed_states.append(q_s)

        while len(unprocessed_states) > 0:
            # process synchronous states
            process_synchronous_state(unprocessed_states.pop())
            if(verbose):
                print(f'Unprocessed states: {unprocessed_states}')
                print(f'Processed states: {processed_states}')

        print(f'Synchronous states done.\n')
        print(f'All states processed, On-line Converter ready')
        self.ready = True
        
    def print_converter(self):
        print(f'Converter statistics:\n - Input alpabet: C = {self._onlineconverter.input_alphabet} \n - Output alphabet: A = {self._onlineconverter.output_alphabet}')
        print(f' - Number of states: {len(self._onlineconverter.states())}')
        print(f' - Delay: delta = {self.delta}\n - Initial zeros: k = {self.k}')
        print(f' - States: Q = {self._onlineconverter.states()}')
        #print(self._onlineconverter.transitions())
        print(f' - Initial state: q_0 = {self._onlineconverter.initial_states()}')
        #print(f' - Terminal states: F = {self._onlineconverter.final_states()}')
        print(f' - Terminal function: omega(Q) = {list(map( lambda q : (q.label(), q.final_word_out), self._onlineconverter.states()))}')
    
        c = self.c
        w = [c,c,c,c,c,c]
        # add padding zeros
        for i in range(self.k):
            w.insert(0,0)

        print(f'Test: Convert the string {w}')
        print(f'Result: {self._onlineconverter.process(w)}')
        #gggg = 1*x + 5
        #print(self._onlineconverter.predecessors(self._onlineconverter.state(x+5)))
        
    def convert(self, input_representation):
        if self.ready:
            # add initial zeros and convert
            for i in range(self.k):
                input_representation.insert(0,0)
            return self._onlineconverter.process(input_representation)
        else:
            print("Converter not ready and shouldn't exist")


# In[2]:


def test():
    OC = OnlineConverter([2,1],4,True)

    OC.convert([4,2])

    print(OC.convert([1,2]))
    @interact
    def _convert(w="221"):
        #nonlocal OC
        input_representation = list(map(int,list(w))) # convert to list of ints
        #pretty_print(latex("Result of conversion : "))
        print(OC.convert(input_representation))


# In[3]:


#test()


# In[ ]:




