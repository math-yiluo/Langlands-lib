# Positive-term conjugation on vector layers

This internal ingredient for the finite vector-bundle filtrations of
supplied relative radicals proves that the first positive term
acts trivially on each actual successive vector quotient. The base ring and
universe are arbitrary, and all equations hold on arbitrary scheme tests,
including nonreduced tests. Zero secondary weights and rank-zero layers are
allowed.

`HeightFiltration.commutator_mem_level_add` is an elementary group-theoretic
extension of the supplied factor commutator sum bound. It assumes that the
target level `a+b` is normal in the ambient group. In the quotient by that
normal level, every factor retained at cutoff `a` commutes with every factor
retained at cutoff `b`, because the original sum bound kills their commutator.
Two applications of subgroup-supremum induction extend this commutation to
the two generated levels. The quotient kernel criterion then places their
original commutator in level `a+b`. Positivity of all original weights is not
assumed.

`RootWeightData.commutator_mem_next` applies this with cutoffs `1` and `d+1`.
The existing `isNormal_subgroup` theorem gives normality of the next actual
root-weight subgroup on the chosen test scheme. Thus the commutator of a
point in `W.subgroup 0` with a point in `W.subgroup d` belongs to
`W.subgroup (d+1)`.

`quotientMap_eq_of_positive_conjugation` takes two actual represented term
points whose ambient images are related by conjugation by a point of
`W.subgroup 0`. Their difference has ambient image equal to the preceding
commutator. The existing all-test `quotientMap_eq_one_iff` therefore kills
that difference and proves equality of the two actual vector-quotient
images. This is a pointwise assertion on every test; it requires no global
lifting or natural-family premise.

`positiveConjugationAction` constructs the actual action of `W.groupScheme 0`
on `W.groupScheme d` by restricting ambient conjugation to the represented
normal subgroup. It retains the actual induced group law of each term.
`positiveConjugationAction_comp` gives its ambient conjugation equation,
and `quotientMap_positiveConjugationAction` proves that composing this action
with the actual quotient map gives the unchanged quotient point.

The provenance is internal: subgroup generation, an ordinary normal-group
quotient and the existing represented root-weight kernel comparison supply
the proof. Full parabolic conjugation linearity, the limit decomposition,
different-torus comparison and the full finite filtration remain separate
obligations.
