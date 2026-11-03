# Descent of a subgroup conjugacy and its source isomorphism

Worker 1333. This is internal descent infrastructure for the unrestricted
rational conjugacy of maximal tori in smooth connected solvable affine groups.
It uses the existing `SubgroupConjugate` relation unchanged. Its hypotheses
explicitly retain a geometric conjugacy witness and a descended or Galois-fixed
conjugator; it does not prove that these witnesses exist for maximal tori.

For any fpqc map of base schemes, monomorphisms `i : H ⟶ G` and
`i' : H' ⟶ G`, and a rational point `g` of `G` over the original base,
`subgroupConjugacyIsoOfBaseChange` constructs an actual isomorphism `H ≅ H'`
from a conjugacy of the pullbacks by the pullback of `g`. The original-field
source isomorphism is constructed, rather than supplied as another premise.
Its defining compatibility is `subgroupConjugacyIsoOfBaseChange_hom_comp`.
Consequently `subgroupConjugate_of_baseChange_conjugacy` gives the unchanged
rational conjugacy conclusion.

The implementation first proves that actual pullback respects inner
automorphisms. The geometric conjugacy identifies the all-test represented
subgroup functors. The published fpqc reflection of represented subgroup
functors descends their equality. The published isomorphism between two
representations of the same subgroup constructs the source isomorphism.
Only monomorphisms are needed here; neither closedness nor torus structure
is required by this internal step.

For a finite-dimensional Galois extension `L/k`, and an affine `G`,
`rationalPointOfGaloisFixed` constructs an original-field rational point from
a fixed rational point of the actual base change. It uses the published
coordinate fixed-point descent, with the published multiplicative
comparisons between coefficient points and rational points. The extension
comparison identifies its pullback with the original fixed point.
`subgroupConjugate_of_galois_fixed_conjugator` then combines this actual point
with fpqc source-isomorphism descent. All fields live in one arbitrary
universe; there is no characteristic, perfection, infinitude or splitness
assumption.

The proof route is derived from the imported descent and represented-subgroup
constructions. Springer, *Linear Algebraic Groups*, second edition (1998),
Theorem 14.4.3, printed p.250 / PDF p.264, motivates its intended use: the last
step descends a conjugator by uniqueness and Galois invariance. This module
only handles a finite-Galois fixed conjugator already supplied as a premise.
It does not establish uniqueness, existence over a separable extension,
rational versus geometric maximality, or the torus-generated and split
unipotent structural reductions. The exact full solvable maximal-torus
conjugacy statement remains a separate proof obligation.
