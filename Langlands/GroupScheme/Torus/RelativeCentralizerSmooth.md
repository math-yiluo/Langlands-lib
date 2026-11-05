# Actual smooth diagonalizable centralizers over arbitrary rings

Let `R` be any commutative ring, and let `G` be an affine group scheme
over `Spec R`. For an actual automorphic action of the diagonalizable
group `D_R(M)` on `G`, `schemeFixedGroupScheme` is the spectrum of the
quotient of the existing affine coordinate algebra of `G` by the
existing `schemeFixedIdeal`. Its group structure and closed inclusion
`schemeFixedHom` come from the corepresented cut-subgroup construction.
No field, noetherian, reducedness or connectedness hypothesis is imposed.
The character group `M` may be any commutative additive group.

The proof first compares the underlying morphism of the existing
coordinate group-scheme isomorphism with `coordinateSchemeIso`.
For every algebra test, the existing
`schemeFixedIdeal_le_ker_iff` then identifies vanishing of the full fixed
ideal with membership in the actual fixed subgroup, pulled back along
that isomorphism. This gives `isCutOutBy_coordinateFixedSubgroup`.
The existing affine-to-all-tests representation theorem identifies
the cut scheme with the actual fixed subgroup on every scheme test.
Transport along the ambient group isomorphism gives
`isRepresentedBy_schemeFixedHom`. Closedness follows from the quotient
construction and this same isomorphism.

If `G` is smooth, its actual coordinate algebra is smooth. The new
finite-equation theorem in `FixedQuotientFinitePresentation` makes
the quotient by the full fixed ideal finitely presented over `R`.
The existing actual-action formal-smoothness theorem
`formallySmooth_schemeFixedQuotient` makes this same quotient formally
smooth. Together these prove its smoothness, hence smoothness of the
constructed group scheme. The result
`fixedSubgroup_hasSmoothClosedRepresentative` records closedness,
smoothness and all-test representability simultaneously.

For conjugation through any actual map `i : D_R(M) → G`,
`Diagonalizable.relativeCentralizerGroupScheme` and
`Diagonalizable.relativeCentralizerHom` specialize this construction.
Their all-test represented subgroup is exactly the existing
`torusCentralizer i`, by the published identification of conjugation
fixedness with that centralizer. The map `i` need not be a closed
immersion. The result
`splitTorusCentralizer_hasSmoothClosedRepresentative_overRing`
then treats any map from an actual split torus: choose its existing
finite-product presentation, identify that split torus with the
appropriate diagonalizable group, and use invariance of the all-test
range under a source isomorphism.

This is an internal derived construction from the existing actual
coordinate action, fixed ideal, corepresented quotient, and all-test
subgroup transport results, together with the finite-equation lemma.
It extends the field-only centralizer smoothness interface without
using its field-dependent projective-quotient argument. It supplies
one relative structural input for reductivity-locus openness.
It does not establish local maximality of a lifted torus, the rank-one
reductivity criterion or openness of that locus.
