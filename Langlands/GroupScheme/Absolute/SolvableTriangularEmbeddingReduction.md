# Rational triangularization gives the concrete closed embedding

Worker 1485.

This module implements the scheme-theoretic passage from rational-point
triangularization to the concrete closed embedding. Its final theorem
`solvableTriangularEmbedding_of_rationalTriangularization` takes
`LieKolchinRationalTriangularizationStatement.{u}` and returns the exact
published `SolvableTriangularEmbeddingStatement.{u}`. Applying it to
`lieKolchinRationalTriangularization` gives the unconditional theorem in
`SolvableTriangularEmbeddingProof`.

For a matrix representation of a smooth group over an algebraically closed field,
`universal_entry_eq_zero_of_rational` compares the regular function given by a
matrix entry with zero. Smoothness makes the source reduced and flat and locally
of finite type. The existing reduced-scheme point extensionality theorem, using
the algebraically closed field as its own algebraic closure, identifies the two
maps to the affine line if their rational-point evaluations agree. The affine
line's representing equivalence then identifies the two global functions.

For decreasing weights `i ↦ -i`, the equations of the existing block parabolic
are precisely vanishing below the diagonal. Thus rational upper triangular
matrices give membership for the universal point, and pullback gives membership
on every test scheme. The closed embedding represents its image subgroup.
The existing represented subgroup lift constructs a factorization through the
concrete block parabolic. Closed immersions cancel against its closed inclusion,
so the factorization is itself a closed immersion.

The assembly applies the published affine linear embedding theorem
`affineLinearEmbeddingStatement` and the published geometric-to-rational
solvability comparison `IsSolvableGroupScheme.rationalPoints`. It invokes
the rational triangularization hypothesis for that actual closed
representation, and postcomposes by the existing inner scheme automorphism.
Postcomposition by this isomorphism preserves the closed immersion. The
factorization above then gives the required actual morphism into the concrete
upper triangular group scheme, together with `IsClosedSubgroup` for it.

This is a derived implementation of the passage from Milne, *Algebraic Groups*
(2017), Theorem 16.30 and Corollary 16.32 (printed pp.334–335) to the closed
embedding form of Proposition 16.2(c) (printed pp.324–325). The registered
source is `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The proof uses the existing scheme and represented-subgroup interfaces rather
than the source's presentation of a faithful trigonalizable representation.
The complete official errata snapshot of 2026-11-02 was checked; its p.324
terminology correction is consistent with this interpretation.

The final implication retains the arbitrary universe `u`, every field
characteristic, dimension zero and every hypothesis of the published target.
The universal-point equations and their pullbacks provide the subgroup
factorization on every test scheme.
