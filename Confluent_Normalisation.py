#!/usr/bin/env python
# coding: utf-8

# In[12]:


from sage.combinat.finite_state_machine import *

# h, ha, ha^2, ... ha^{m-1}:
def process_middle_state_left(NormaliserLeft,middle_state, number_of_loaded_a,a,b,m, verbose):
    if number_of_loaded_a < m - 1:
        # add transitions for letters less than a
        for h in range(a):
            # h/h'a^k transition to h
            transHH = FSMTransition(middle_state,NormaliserLeft.state(f'{h}'),h,middle_state.final_word_out)
            NormaliserLeft.add_transition(transHH)
        # add next middle state and transition for a
        next_final_word = middle_state.final_word_out + [a]
        next_label = ''.join(map(str,next_final_word))
        middle_state_next = FSMState(next_label,is_final=True, final_word_out=next_final_word)
        # a/epsilon transition to next middle state
        transHA = FSMTransition(middle_state,middle_state_next, a, None)
        NormaliserLeft.add_state(middle_state_next)
        NormaliserLeft.add_transition(transHA)
        if(verbose):
            print(f'added next left middle state {middle_state_next} with {transHA} and output word {next_final_word}')
        
        # recursively process next state
        process_middle_state_left(NormaliserLeft,middle_state_next, number_of_loaded_a + 1,a,b,m,verbose)
    else:
        # we've reached ha^{m-1}
        if(verbose):
            print(f'Reached final left middle state {middle_state}')
        # add transitions for letters less than b
        for u in range(b):
            transUHamminus1 = FSMTransition(middle_state,NormaliserLeft.state(f'{u}'),u,middle_state.final_word_out)
            NormaliserLeft.add_transition(transUHamminus1)
            if(verbose):
                print(f'added {transUHamminus1}')

        # prepare output word in case the next letter is at least b (when we perform the reduction)
        output_word_reduced = deepcopy(middle_state.final_word_out)
        output_word_reduced[0] += 1
        for i in range(1, len(output_word_reduced)):
            output_word_reduced[i] = 0
        if(verbose):
            print(f'output_word_reduced: {output_word_reduced} ')
        # add transitions for letters greater than b
        for k in range(b,a+1):
            kminb = k-b
            transKHplus1zeromminus1 = FSMTransition(middle_state,NormaliserLeft.state(f'{kminb}'),k,output_word_reduced)
            NormaliserLeft.add_transition(transKHplus1zeromminus1)
            if(verbose):
                print(f'added {transKHplus1zeromminus1}')

# returns left normaliser (Gamma)
def left_normaliser(Basis_coefficients, verbose=True):
    # assumes we already know that the basis is confluent
    a = Basis_coefficients[0]
    b = Basis_coefficients[len(Basis_coefficients)-1]
    m = len(Basis_coefficients)
    A = list(range(a+1))
    print('Building left normaliser...')
    NormaliserLeft = Transducer(input_alphabet=A, output_alphabet=A)
    q_eps = FSMState('', is_final=True, is_initial=True,final_word_out=[])
    NormaliserLeft.add_state(q_eps)
    transAA = FSMTransition('','',a,a)
    NormaliserLeft.add_transition(transAA)
    for h in range(a):
        q_h = FSMState(f'{h}',is_final=True, final_word_out=[h])
        transHEps = FSMTransition(q_eps,q_h,h,None)
        NormaliserLeft.add_state(q_h)
        NormaliserLeft.add_transition(transHEps)
    for h in range(a):
        process_middle_state_left(NormaliserLeft,NormaliserLeft.state(f'{h}'),0,a,b,m, verbose)
    
    print('Left normaliser finished')
    return NormaliserLeft


def process_middle_state_right(NormaliserRight,middle_state, number_of_loaded_a,a,b,m, verbose):
    if number_of_loaded_a < m - 1:
        if(verbose):
            print(f'processing right middle state {middle_state}:')
        # add transitions for letters less than b back to epsilon state
        for u in range(b):
            transUAK = FSMTransition(middle_state,NormaliserRight.state(''),u,middle_state.final_word_out + [u])
            NormaliserRight.add_transition(transUAK)
            if(verbose):
                print(f' - added {transUAK}')
        # add transitions for letters less than a to other states
        for x in range(b,a):
            transXK = FSMTransition(middle_state,NormaliserRight.state(f'{x}'),x,middle_state.final_word_out)
            NormaliserRight.add_transition(transXK)
            if(verbose):
                print(f' - added {transXK}')
        # add next middle state and transition for a
        next_final_word = middle_state.final_word_out + [a]
        if next_final_word == [a]*m:
            if(verbose):
                print('got a transition to a^m')
            # a/epsilon transition to next middle state
            transHA = FSMTransition(middle_state,NormaliserRight.state(str(a)*m), a, middle_state.final_word_out[0])
            NormaliserRight.add_transition(transHA)
            if(verbose):
                print(f' - added {transHA}')
            # recursively process next state
            process_middle_state_right(NormaliserRight,NormaliserRight.state(str(a)*m), number_of_loaded_a + 1,a,b,m,verbose)
        else:
            next_label = ''.join(map(str,next_final_word))
            middle_state_next = FSMState(next_label,is_final=True, final_word_out=next_final_word)
            # a/epsilon transition to next middle state
            transHA = FSMTransition(middle_state,middle_state_next, a, None)
            NormaliserRight.add_state(middle_state_next)
            NormaliserRight.add_transition(transHA)
            if(verbose):
                print(f' - added {transHA}')
                print(f'created new right middle state {middle_state_next} with output word {next_final_word}')
        
            # recursively process next state
            process_middle_state_right(NormaliserRight,middle_state_next, number_of_loaded_a + 1,a,b,m,verbose)
    else:
        # we've reached a^{m-1}k (in our case actually state ka^{m-1})
        if(verbose):
            print(f'Reached final right middle state {middle_state}')
        output_word_reduced = deepcopy(middle_state.final_word_out)
        # prepare output word
        output_word_reduced[0] -= b
        for i in range(1, len(output_word_reduced)):
            output_word_reduced[i] = 0
            
        # add transitions for letters less than b-1 back to epsilon state
        for t in range(b - 1):
            transTTplus1zerommin1kmib = FSMTransition(middle_state,NormaliserRight.state(''),t,[t+1] + output_word_reduced)
            NormaliserRight.add_transition(transTTplus1zerommin1kmib)
            if(verbose):
                print(f' - added {transTTplus1zerommin1kmib}')
        # add transitions for letters less than a to next states
        for y in range(b-1,a):
            transZerommin1kminb = FSMTransition(middle_state,NormaliserRight.state(f'{y+1}'),y,output_word_reduced)
            NormaliserRight.add_transition(transZerommin1kminb)
            if(verbose):
                print(f' - added {transZerommin1kminb}')
        # add transition for a
        am_label = str(a)*m
        transAK = None
        if middle_state == NormaliserRight.state(am_label):
            if(verbose):
                print(f'{middle_state} is equal to {NormaliserRight.state(am_label)}')
            transAK = FSMTransition(middle_state,middle_state,a,middle_state.final_word_out[0])
            NormaliserRight.add_transition(transAK)
        else:
            transAK = FSMTransition(middle_state,NormaliserRight.state(am_label),a,middle_state.final_word_out[0])
            NormaliserRight.add_transition(transAK)
            if(verbose):
                print(f' - added {transAK}')
        

# returns right normaliser (Delta)
def right_normaliser(Basis_coefficients, verbose=True):
    print('Building right normaliser...')
    # right normaliser = reads string from right
    # before process()ing a string in this, call reverse() on it and then reverse() the output
    # assumes we already know that the basis is confluent
    a = Basis_coefficients[0]
    b = Basis_coefficients[len(Basis_coefficients)-1]
    m = len(Basis_coefficients)
    A = list(range(a+1))
    NormaliserRight = Transducer(input_alphabet=A, output_alphabet=A)
    q_eps = FSMState('', is_final=True, is_initial=True,final_word_out=[])
    NormaliserRight.add_state(q_eps)
    # self-transitions for letters less than b
    for u in range(b):
        transUU = FSMTransition(q_eps,q_eps,u,u)
        NormaliserRight.add_transition(transUU)
    # for letters greater than b
    for k in range(b,a+1):
        q_k = FSMState(f'{k}',is_final=True, final_word_out=[k])
        transKEps = FSMTransition(q_eps,q_k,k,None)
        NormaliserRight.add_state(q_k)
        NormaliserRight.add_transition(transKEps)
    # lastly, add the a^m state (will be connected eventually)
    q_am = FSMState(f'{str(a)*m}', is_final=True, final_word_out = [a]*m)
    NormaliserRight.add_state(q_am)
    if(verbose):
        print(f'added state {q_am}')
    
    for k in range(b,a+1):
        process_middle_state_right(NormaliserRight,NormaliserRight.state(f'{k}'),0,a,b,m,verbose)
    
    print('Right normaliser finished')
    return NormaliserRight

#Construct normalisers
#Basis_coeffs = [3,3,1]
#Gamma = left_normaliser(Basis_coeffs, False)
#Delta = right_normaliser(Basis_coeffs, False)


# In[12]:


def wave_reduction_test(Converter,left = True):
    w = [0,a,a,a,a,a,a,b]
    w2 = [0,a,b-1,a,a,b-1,a,a,a,b-1,a,a,a,a,b-1]

    if(left):
        print(f'Test: Convert the string {w}')
        print(f'Result: {Converter.process(w)}')
        print(f'Test: Convert the string {w2}')
        print(f'Result: {Converter.process(w2)}')
    else:
        w.reverse()
        w2.reverse()
        print(f'Test: Convert the string {w}')
        Result = Converter.process(w)
        #Result[2].reverse()
        print(f'Result: {Result}')
        print(f'Test: Convert the string {w2}')
        Result2 = Converter.process(w2)
        #Result2[2].reverse()
        print(f'Result: {Result2}')

def print_converter(Converter):
    print(f'Converter statistics:\n - Input alpabet: A = {Converter.input_alphabet} \n - Output alphabet: A = {Converter.output_alphabet}')
    print(f' - States: Q = {Converter.states()}')
    #print(OnLineConverter.transitions())
    print(f' - Number of states: {len(Converter.states())}')
    print(f' - Initial state: q_0 = {Converter.initial_states()}')
    print(f' - Terminal states: F = {Converter.final_states()}')
    print(f' - Terminal function: omega(Q) = {list(map( lambda q : (q.label(), q.final_word_out), Converter.states()))}')
    #print(f' - Delay: delta = {delta}\n - Initial zeros: k = {k}')
    print(f' - Transitions: {Converter.transitions()}')
    
    #PPPPP = Converter.predecessors(Converter.state('22'))
    #print(f'{PPPPP}')
    # demonstration of "waves of reduction"
    wave_reduction_test(Converter)
    wave_reduction_test(Converter,False)

#print('Left normaliser: ')
#print_converter(Gamma)
#print('\nRight normaliser: ')
#print_converter(Delta)

def normalise(LeftNormaliser, RightNormaliser, inputString):
    output = []
    # add a zero at the start
    inputString.insert(0,0)
    # run through the left normaliser
    result = LeftNormaliser.process(inputString)
    if (result[0] == True):
        output = result[2]
        output.reverse()
    else:
        return []
    # reverse and run through right normaliser
    result = RightNormaliser.process(output)
    if (result[0] == True):
        output = result[2]
        # reverse the result and return
        output.reverse()
        return output
    else:
        return []

#W = [a,a,a,a,a,a,b-1,a,a,a]
#print(f'Normal form of {W}: {normalise(Gamma, Delta, W)}')

