from aimacode.logic import PropKB
from aimacode.planning import Action
from aimacode.search import (
    Node, Problem,
)
from aimacode.utils import expr
from lp_utils import (
    FluentState, encode_state, decode_state,
)
from my_planning_graph import PlanningGraph

from functools import lru_cache


class AirCargoProblem(Problem):
    def __init__(self, cargos, planes, airports, initial: FluentState, goal: list):
        """

        :param cargos: list of str
            cargos in the problem
        :param planes: list of str
            planes in the problem
        :param airports: list of str
            airports in the problem
        :param initial: FluentState object
            positive and negative literal fluents (as expr) describing initial state
        :param goal: list of expr
            literal fluents required for goal test
        """
        self.state_map = initial.pos + initial.neg #this is passed in by the problem definition
        self.initial_state_TF = encode_state(initial, self.state_map)
        Problem.__init__(self, self.initial_state_TF, goal = goal)
        self.cargos = cargos
        self.planes = planes
        self.airports = airports
        self.actions_list = self.get_actions() #this is permutation of all possible actions

    def get_actions(self):
        """
        This method creates concrete actions (no variables) for all actions in the problem
        domain action schema and turns them into complete Action objects as defined in the
        aimacode.planning module. It is computationally expensive to call this method directly;
        however, it is called in the constructor and the results cached in the `actions_list` property.

        Returns:
        ----------
        list<Action>
            list of Action objects
        """

        # TODO create concrete Action objects based on the domain action schema for: Load, Unload, and Fly
        # concrete actions definition: specific literal action that does not include variables as with the schema
        # for example, the action schema 'Load(c, p, a)' can represent the concrete actions 'Load(C1, P1, SFO)'
        # or 'Load(C2, P2, JFK)'.  The actions for the planning problem must be concrete because the problems in
        # forward search and Planning Graphs must use Propositional Logic

        def load_actions():
            """Create all concrete Load actions and return a list

            :return: list of Action objects
            
            Load(c, p, a), #cargo, plan, airport
            PRECOND: At(c, a) ∧ At(p, a) ∧ Cargo(c) ∧ Plane(p) ∧ Airport(a)
            EFFECT: ¬ At(c, a) ∧ In(c, p)
            """
            loads = []
            # TODO create all load ground actions from the domain Load action
            for airport in self.airports:
                for plane in self.planes:
                    for cargo in self.cargos:
                        precond_pos = [expr("At({}, {})".format(cargo, airport)),
                                       expr("At({}, {})".format(plane, airport)),
                                       ]
                        precond_neg = []
                        effect_add = [expr("In({}, {})".format(cargo, plane))]
                        effect_rem = [expr("At({}, {})".format(cargo, airport))]
                        load = Action(expr("Load({}, {}, {})".format(cargo, plane, airport)),
                                      [precond_pos, precond_neg],
                                      [effect_add, effect_rem])
                        loads.append(load)
            return loads

        def unload_actions():
            """Create all concrete Unload actions and return a list

            :return: list of Action objects
            Unload(c, p, a),
            PRECOND: In(c, p) ∧ At(p, a) ∧ Cargo(c) ∧ Plane(p) ∧ Airport(a)
            EFFECT: At(c, a) ∧ ¬ In(c, p)
            """
            unloads = []
            # TODO create all Unload ground actions from the domain Unload action
            for airport in self.airports:
                for plane in self.planes:
                    for cargo in self.cargos:
                        precond_pos = [expr("In({}, {})".format(cargo, plane)),
                                       expr("At({}, {})".format(plane, airport)),
                                       ]
                        precond_neg = []
                        effect_add = [expr("At({}, {})".format(cargo, airport))]
                        effect_rem = [expr("In({}, {})".format(cargo, plane))]
                        unload = Action(expr("Unload({}, {}, {})".format(cargo, plane, airport)),
                                      [precond_pos, precond_neg],
                                      [effect_add, effect_rem])
                        unloads.append(unload)
            return unloads

        def fly_actions():
            """Create all concrete Fly actions and return a list

            :return: list of Action objects

            Fly(p, from, to),
            PRECOND: At(p, from) ∧ Plane(p) ∧ Airport(from) ∧ Airport(to)
            EFFECT: ¬ At(p, from) ∧ At(p, to)
            """
            flys = []
            for fr in self.airports:
                for to in self.airports:
                    if fr != to:
                        for p in self.planes:
                            precond_pos = [expr("At({}, {})".format(p, fr)),
                                           ]
                            precond_neg = []
                            effect_add = [expr("At({}, {})".format(p, to))]
                            effect_rem = [expr("At({}, {})".format(p, fr))]
                            fly = Action(expr("Fly({}, {}, {})".format(p, fr, to)),
                                         [precond_pos, precond_neg],
                                         [effect_add, effect_rem])
                            flys.append(fly)
            return flys

        return load_actions() + unload_actions() + fly_actions()

    def actions(self, state: str) -> list:
        """ Return the actions that can be executed in the given state.

        :param state: str
            state represented as T/F string of mapped fluents (state variables)
            e.g. 'FTTTFF'
        :return: list of Action objects
        """
        # TODO implement
        possible_actions = []
        kb = PropKB()
        kb.tell(decode_state(state, self.state_map).pos_sentence()) #the only true states are loaded into the kb.clauses
        for action in self.actions_list:
            #print(action, action.precond_pos, action.precond_neg, action.effect_add)
            #print(kb.clauses)
            is_possible = True
            for clause in action.precond_pos:
                if clause not in kb.clauses:
                    is_possible = False
            for clause in action.precond_neg:
                if clause in kb.clauses:
                    is_possible = False
            if is_possible:
                #print('possible', action)
                possible_actions.append(action)
            #else:
                #print('not possible', action)
        return possible_actions

    def result(self, state: str, action: Action):
        """ Return the state that results from executing the given
        action in the given state. The action must be one of
        self.actions(state).

        :param state: state entering node
        :param action: Action applied
        :return: resulting state after action
        """
        # TODO implement
        new_state = FluentState([], [])
        old_state = decode_state(state, self.state_map)
        for fluent in old_state.pos:
            if fluent not in action.effect_rem:
                new_state.pos.append(fluent)
        for fluent in action.effect_add:
            if fluent not in new_state.pos:
                new_state.pos.append(fluent)
        for fluent in old_state.neg:
            if fluent not in action.effect_add:
                new_state.neg.append(fluent)
        for fluent in action.effect_rem:
            if fluent not in new_state.neg:
                new_state.neg.append(fluent)
                
        return encode_state(new_state, self.state_map)

    def goal_test(self, state: str) -> bool:
        """ Test the state to see if goal is reached

        :param state: str representing state
        :return: bool
        """
        kb = PropKB()
        kb.tell(decode_state(state, self.state_map).pos_sentence())
        for clause in self.goal:
            if clause not in kb.clauses:
                return False
        return True

    def h_1(self, node: Node):
        # note that this is not a true heuristic
        h_const = 1
        return h_const

    @lru_cache(maxsize=8192)
    def h_pg_levelsum(self, node: Node):
        """This heuristic uses a planning graph representation of the problem
        state space to estimate the sum of all actions that must be carried
        out from the current state in order to satisfy each individual goal
        condition.
        """
        # requires implemented PlanningGraph class
        pg = PlanningGraph(self, node.state)
        pg_levelsum = pg.h_levelsum()
        return pg_levelsum

    @lru_cache(maxsize=8192)
    def h_ignore_preconditions(self, node: Node):
        """This heuristic estimates the minimum number of actions that must be
        carried out from the current state in order to satisfy all of the goal
        conditions by ignoring the preconditions required for an action to be
        executed.

        When evaluating the ignore preconditions heuristic, you are given a Node object that
        describes the current state. You want to answer this question:
        "What is the minimum number of actions you'll need to take to satisfy all your goals?"
        In our code, we assume that the goals are satisfied by different actions, so if you have
        3 goal states, it would require at least 3 actions to satisfy them.
        So what you really want to do is figure out how many of the goal states are not yet
        satisfied in the current state. Because the number of unsatisfied goals equals the
        minimum number of actions you would need to take to satisfy them all.

        """
        # TODO implement (see Russell-Norvig Ed-3 10.2.3  or Russell-Norvig Ed-2 11.2)
        if True:
            poss_act_eff = []
            for action in self.actions_list:
                if node.action == action:
                    poss_act_eff.append(action.effect_add[0])
            if poss_act_eff in self.goal:
                return 1
            return 2
        else: #udacity suggestion, not working
            count = 0
            for i, fluent in enumerate(self.state_map):
            #count number of fluents not correct
                if fluent in self.goal:
                    if node.state[i] == 'F':
                        return count

def air_cargo_p1() -> AirCargoProblem:
    cargos = ['C1', 'C2']
    planes = ['P1', 'P2']
    airports = ['JFK', 'SFO']

    #these are not preconditions, there are just the T&F that at the very beginning of the exercise
    #note that these are all the avaiable fluents, and may change between T and F depending on the state
    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)'),
           ]
    
    neg = [expr('At(C2, SFO)'),
           expr('In(C2, P1)'),
           expr('In(C2, P2)'),
           expr('At(C1, JFK)'),
           expr('In(C1, P1)'),
           expr('In(C1, P2)'),
           expr('At(P1, JFK)'),
           expr('At(P2, SFO)'),
           ]
    
    init = FluentState(pos, neg)
    
    goal = [expr('At(C1, JFK)'),
            expr('At(C2, SFO)'),
            ]
    
    return AirCargoProblem(cargos, planes, airports, init, goal)


def air_cargo_p2() -> AirCargoProblem:
    # TODO implement Problem 2 definition
    cargos = ['C1', 'C2', 'C3']
    planes = ['P1', 'P2', 'P3']
    airports = ['SFO', 'JFK', 'ATL']

    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),
           expr('At(C3, ATL)'),
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)'),
           expr('At(P3, ATL)'),
           ]
    
    neg = [expr('At(C2, SFO)'),
           expr('At(C2, ATL)'),
           expr('In(C2, P1)'),
           expr('In(C2, P2)'),
           expr('In(C2, P3)'),
           
           expr('At(C1, JFK)'),
           expr('At(C1, ATL)'),
           expr('In(C1, P1)'),
           expr('In(C1, P2)'),
           expr('In(C1, P3)'),

           expr('At(C3, SFO)'),
           expr('At(C3, JFK)'),
           expr('In(C3, P1)'),
           expr('In(C3, P2)'),
           expr('In(C3, P3)'),
           
           expr('At(P1, JFK)'),
           expr('At(P1, ATL)'),
           
           expr('At(P2, SFO)'),
           expr('At(P2, ATL)'),

           expr('At(P3, SFO)'),
           expr('At(P3, JFK)'),
           ]
    
    init = FluentState(pos, neg)
    
    goal = [expr('At(C1, JFK)'),
            expr('At(C2, SFO)'),
            expr('At(C3, SFO)'),
            ]
    
    return AirCargoProblem(cargos, planes, airports, init, goal)


def air_cargo_p3() -> AirCargoProblem:
    # TODO implement Problem 3 definition
    cargos = ['C1', 'C2', 'C3', 'C4']
    planes = ['P1', 'P2']
    airports = ['SFO', 'JFK', 'ATL', 'ORD']

    pos = [expr('At(C1, SFO)'),
           expr('At(C2, JFK)'),
           expr('At(C3, ATL)'),
           expr('At(C4, ORD)'),
           
           expr('At(P1, SFO)'),
           expr('At(P2, JFK)'),
           ]

    neg = [expr('At(C1, JFK)'),
           expr('At(C1, ATL)'),
           expr('At(C1, ORD)'),
           expr('In(C1, P1)'),
           expr('In(C1, P2)'),

           expr('At(C2, SFO)'),
           expr('At(C2, ATL)'),
           expr('At(C2, ORD)'),
           expr('In(C2, P1)'),
           expr('In(C2, P2)'),

           expr('At(C3, SFO)'),
           expr('At(C3, JFK)'),
           expr('At(C3, ORD)'),
           expr('In(C3, P1)'),
           expr('In(C3, P2)'),

           expr('At(C4, SFO)'),
           expr('At(C4, JFK)'),
           expr('At(C4, ATL)'),
           expr('In(C4, P1)'),
           expr('In(C4, P2)'),
           
           expr('At(P1, JFK)'),
           expr('At(P1, ATL)'),
           expr('At(P1, ORD)'),
           
           expr('At(P2, SFO)'),
           expr('At(P2, ATL)'),
           expr('At(P2, ORD)'),
           ]
    
    init = FluentState(pos, neg)
    
    goal = [expr('At(C1, JFK)'),
            expr('At(C2, SFO)'),
            expr('At(C3, JFK)'),
            expr('At(C4, SFO)'),
            ]
    
    return AirCargoProblem(cargos, planes, airports, init, goal)

if __name__ == '__main__':
    from aimacode.search import (
        breadth_first_search, astar_search, depth_first_graph_search,
        uniform_cost_search, greedy_best_first_graph_search)
    import run_search

    # the problem is the air cargo problem
    # it takes in cargo (input options), planes (input options), airports (input options), initial fluent states(pos and neg), and goals
    # initial fluent states are a bunch of positive and negative expressions that limits the combinations of inputs at the initial stage
    # state_map is the combination of pos and neg fluents, translate into True or False 
    # goal contains a bunch of expressions that we want to satisfy at the same time
    # initial_state_TF is the fluent state translate into positive or negative fluents, indicated by True or False
    
    # for this problem's actions_list, there's 3 types of actions: fly, load, unload. each action is a combination of the available inputs
    # the action class is initialized with name(string), args(input tuples), preconditions(expressions), and effects(expressions)
    # this is all the available actions for the problem, and we are also listing their preconditions as well as their effects
    
    p = air_cargo_p1()

    print("**** want to look at how the problem works ****")
    print("TESTING!!!!!!!!!!")
    
    if True: #the solution is correct
        print("*** Breadth First Search")
        run_search.run_search(p, breadth_first_search)
        
    if True: #the solution is correct, but terrible
        print("*** Depth First Search")
        run_search.run_search(p, depth_first_graph_search)
        
    if True: #the solution is correct, seems like it performs better than breath first
        print("*** Uniform Cost Search")
        run_search.run_search(p, uniform_cost_search)

    if True: #the solution is correct, 
        print("*** Greedy Best First Graph Search - null heuristic")
        run_search.run_search(p, greedy_best_first_graph_search, parameter = p.h_1)

    if True: #the solution is correct, 
        print("*** A-star null heuristic")
        run_search.run_search(p, astar_search, p.h_1)

    if True:
        print("A-star ignore preconditions heuristic")
        run_search.run_search(p, astar_search, p.h_ignore_preconditions)
    
    if True:
        print("A-star levelsum heuristic")
        run_search.run_search(p, astar_search, p.h_pg_levelsum)

    

    # the problem is setup as the initial conditions/states. We will use the available actions to get us to the defined goal
    if False:
        print('here are the available inputs:')
        print('cargo: ', p.cargos)
        print('airplanes: ', p.planes)
        print('airport: ', p.airports)
        print('heres how the problem is setup:')
        print('all fluents: ', p.state_map)
        print('fluents by T/F: ', p.initial_state_TF)
        print('our ultimate goal: ', p.goal)
        print('heres a list of available actions:')
        print('action, name, arg, precond pos, precon neg, effect pos, effect neg')
        for a in p.actions_list:
            print(a, a.name, a.args, a.precond_pos, a.precond_neg, a.effect_add, a.effect_rem)
        pause = input('wait...')

    # the actions method returns possible actions. it is based on comparing the state fluent and preconditions
    if False:
        print('actions testing')
        print(p.actions('FTTTFFFFFFFF'))
        pause = input('wait...')
        
