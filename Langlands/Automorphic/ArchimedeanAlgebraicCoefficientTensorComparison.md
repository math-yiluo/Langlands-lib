# Actual automorphic tensor comparison of analytic and algebraic coefficients

This internal construction tensors the actual full-carrier coefficient Lie
equivalence `analyticAlgebraicLieEquiv` with the identity on the original
automorphic realization. The existing actual tensor equivalence construction
gives `tensorAnalyticAlgebraicLieEquiv`, comparing the diagonal full complex Lie
actions on `S.Space ⊗[ℂ] AnalyticSpace e ρ` and
`S.Space ⊗[ℂ] Space e ρ`. On a pure tensor its value is
`f ⊗ analyticCoordinates e ρ v`, retaining the automorphic vector.

Tensoring the original compact coefficient equivalence with that same
automorphic identity gives `tensorAnalyticAlgebraicCompactEquiv`. Its application
lemma proves that its map is the same as the tensor Lie equivalence's map.
The original finite adelic translations also intertwine with that map, by the
published finite compatibility of actual tensor equivalences.

`algebraicTensorReducedLieRingModule` and `algebraicTensorReducedLieModule`
restrict the original algebraic diagonal action through
`reducedComplexInclusion`. The explicit pure-tensor bracket formula identifies
the second-factor operator as the original algebraic `lieAction e ρ`, while
the first factor remains the original automorphic differential.
`tensorAnalyticAlgebraicReducedLieEquiv` restricts the full tensor equivalence
to these actual reduced Lie modules. Its underlying map is unchanged.

`tensorAnalyticAlgebraicHorizontalEquiv` uses the same original compact
coefficient equivalence to give an equivalence of the already constructed
horizontal finite adelic representations in every degree. Its value on each
Lie tuple is postcomposition by the same reduced tensor Lie equivalence; the
whole-alternating-map formula identifies it with the published coefficient
cochain `map`.

`tensorAnalyticAlgebraicCochain_differential` applies actual coefficient
differential functoriality to this reduced Lie equivalence. It proves
commutation with the analytic and algebraic Chevalley–Eilenberg differentials
on all reduced cochains. This uses their original coefficient actions; the
desired differential compatibility is not supplied as a premise.

The number-field universe remains independent of the small finite
selected-embedding and coefficient indices. Both complex-place orientations,
all original automorphic and coefficient vectors, empty indices, rank zero
and every cochain degree are retained. This pair requires no positive-rank
hypothesis: it does not use the split-center retraction or construct the
algebraic horizontal quotient cohomology. Those quotient constructions and
their comparison are subsequent work.

The provenance is internal composition of the actual coefficient comparison,
original tensor equivalences, full compact horizontal spaces and genuine
coefficient differential functoriality. No new original-source correspondence
is claimed.
