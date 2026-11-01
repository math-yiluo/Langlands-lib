# Interfaces for the actual I.2.4 induction statements

Worker 691 supplies internal interface checks for the three unproved targets in
`NondegenerateInductionExactnessStatements`. Their mathematical provenance and
source locators are in that module's paired Markdown: Renard (9 July 2026),
I.2.4, printed pp.18–19 / PDF24–25, with A.VIII.1–2, PDF272–273.
These checks do not assume or prove any principal target.

Complete unapplied checks give each target exactly type `Prop`, at independent
`uA,uB,v`, both unequal ring assignments `(0,1)` and `(1,0)`, and `(2,0,0)`,
where the A-universe is strictly above both carrier levels. Exact unfolding
equalities expose every internally bound ring, original action,
idempotentedness, commutation and source nondegeneracy input. They also expose
the named abelian data, full sequence predicates, actual functors and common
carrier specialization for injectivity.

The A–B and B–A sections are independent. Each gives the actual domain and
target at arbitrary source carrier `v` and target carrier `max uB v`.
Definitional equalities retain the actual tensor or Hom-part carriers,
their chosen additive groups and residual actions, whole original maps,
tensor generator formulas, source-precomposition action and restricted
postcomposition. The published additive instances are checked. The named
abelian structure's inherited preadditive equality is reused.
Sequence unfoldings retain every one-sided exact short complex and the
boundary monomorphism or epimorphism.

At the common carrier `max uB v`, a definitional type equality checks absorption
of the repeated maximum. The actual I has that common domain and codomain.
The published `Langlands.Renard.homInjectiveComparison` checks the equivalence
of source exact-Hom and Mathlib injectivity, including equivalence of the two
preservation implications. This proves only equivalence of formulations.

The `CompetingStructures` section keeps alternative ring and module structures
in scope and checks which instances are inferred there. Explicit arguments and
local bindings then retain the specified source rings, their additive groups,
the chosen original action and exactly the named regular opposite-side action
in the actual functor object formulas. These equalities use reflexivity after
introducing the module object.

The integer examples use the regular left and right actions on ℤ, the published
idempotentedness and nondegeneracy results, and the regular nondegenerate object.
They check tensor object formulas and that all three specialized conclusions
form propositions. The subsingleton examples instantiate the actual tensor
functors when B is a zero ring, and construct trivial nondegenerate modules at
arbitrary carrier universes. Their nondegeneracy witness is the idempotent zero
acting on a subsingleton group, including `PUnit` with its zero action.
No zero action on a nonzero group is asserted to be nondegenerate.

Worker 490 contributed the source and contract audit and the check of complete
prerequisite publication; Worker 691 implemented these interface checks.
