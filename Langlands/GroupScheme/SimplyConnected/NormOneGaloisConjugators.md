# Actual Galois conjugators of a norm-one splitting chart

This internal construction obtains matrices from the original splitting
chart, rather than supplying Galois intertwiners as hypotheses.

For each ground-field automorphism `sigma` of the splitting field,
`galoisChart` first applies the inverse coefficient action on `L ⊗ A`,
then the original chart and finally `sigma` entrywise. This is proved to
be linear over `L`. The published matrix-chart comparison theorem gives
an invertible matrix `galoisConjugator` implementing the comparison of
these two actual charts.

The resulting convention is
`P_sigma e(1 tensor a) = sigma(e(1 tensor a)) P_sigma`. Its extension to
every matrix identifies the chart-induced coefficient action with
twisted coefficient conjugation. Consequently the actual fixed
subalgebra is exactly the matrices satisfying
`P_sigma X = sigma(X) P_sigma` for every `sigma`.

The coefficient-algebra extension theorem uses tensor induction to
prove the same identity for the actual extended charts over arbitrary
coefficient algebras. `galoisConjugator_normOneChartPoints` applies it to
the actual norm-one points over every scheme test and point of the
splitting field. Composing the splitting-field point with `sigma`
shifts its scalar chart, and the constructed matrix intertwines those
two actual chart matrices.

For any Galois splitting extension, including infinite extensions,
`fixedEquivOfIsGalois` identifies the original algebra with the actual
fixed matrix subalgebra, by the map `a` to `e(1 tensor a)`.
Injectivity is faithful scalar extension. Surjectivity uses the
companion noncommutative fixed-tensor theorem
`GaloisAlgebraDescent.mem_range_includeRight_iff_of_isGalois`: a fixed
tensor has original-field coordinates in a basis of the original
algebra. Thus this algebra recovery also applies to a separable-closure
chart, without a finite-extension or effectivity premise.

The chart and conjugator construction itself requires no Galois
hypothesis. Only the algebra recovery assumes that the field extension
is Galois. The all-test norm-one specialization assumes that the
original algebra is central simple. All three fields/algebras may lie
in the same arbitrary universe `u`, and no characteristic, perfection,
continuity or centre-smoothness condition is imposed.

Provenance is internal: the construction uses actual coefficient
actions, the published theorem that two full matrix charts differ by
unit conjugation, and the original norm-one chart. It proves the
conjugators' required equations rather than postulating them. It does
not yet assert equality with the general coefficient-generated Tits
algebra or its Brauer class.
