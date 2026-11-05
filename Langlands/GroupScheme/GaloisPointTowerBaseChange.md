# Direct and iterated base changes in a field tower

For a compatible tower of fields `k → L → M`, `towerBaseChangeIso` identifies
`(G_L)_M` with `G_M`. It is the standard pullback composition isomorphism,
followed by the equality of the composite base map with the direct base map.
Its first-projection formula shows that its action on rational points has the
same original coefficient point as the two successive base-change comparisons.

For an affine commutative group scheme and a finite Galois extension `M/L`,
`relativeRationalNorm_towerBaseChangeIso` identifies the relative norm between
the direct base changes with the ordinary rational norm of `T_L` after this
isomorphism. The proof applies the coefficient comparison, uses its compatibility
with the ordinary norm, and then uses the projection formula. No finiteness or
Galois condition on `L/k` is needed for this comparison.

This is internal pullback infrastructure for the tower argument in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.5.12,
printed pp.89–90 (PDF pp.120–121). It asserts neither bounded norm surjectivity
nor splitting-field independence.
