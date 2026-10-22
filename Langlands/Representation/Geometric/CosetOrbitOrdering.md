# Double cosets and finite action orbit ordering

This internal construction connects the actual Mathlib double-coset quotient to
the orbit quotient for the published inverse right action on `Induction.LeftQuotient P`.
It also gives a conditional reduction of `ClosedSubgroupOrbitOrdering` to the
published proposition `Langlands.Topology.FiniteOrbitOrdering`. It does not prove
that general proposition or the unconditional closed-subgroup ordering theorem.

The relation lemma `leftQuotientAction_orbitRel_iff` uses the orbit formula from
`CosetAction` and the membership criterion from `OrbitRepresentatives`. For group
elements `g,h`, the points `P g` and `P h` are in the same action orbit precisely
when their double-coset classes agree. No topology is used in this lemma.

`doubleCosetEquivOrbitQuotient` sends the double-coset class of `g` to the action
orbit class of `P g`. The relation lemma makes this well-defined and injective;
quotient induction twice proves surjectivity. Its representative formula is
recorded by `doubleCosetEquivOrbitQuotient_mk`. The theorem
`finite_leftQuotientAction_orbits` transports finiteness through this equivalence.

For the conditional reduction, the closed subgroup `Q` is sigma compact, and
`P \ G` is locally compact and Hausdorff by the published quotient topology API.
The inverse right action is jointly continuous. The supplied general ordering
proposition therefore yields representatives in `P \ G`, a disjoint orbit cover,
and open initial unions. Choose group lifts `g i` of these quotient points and
use `(g i)⁻¹` as the representatives in `OrderedDoubleCosets`; this preserves
exactly the convention `P w⁻¹ Q`. Equality of each orbit transports the three
ordering fields without changing the quotient topology.

The construction is derived from the imported definitions and elementary
quotient reasoning. The conditional theorem retains the full group universe and
all hypotheses of the original closed-subgroup target. It supplies no Mackey
graded-piece assertion or further representation-theoretic conclusion.
