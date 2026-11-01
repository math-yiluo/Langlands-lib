# Normalized adjacent-rank compact sections on the original carrier

This module specializes the compact rectangular average to the exact canonical
normalized opposite-parabolic induction in `AdjacentRankModelImageStatement`.
It implements the section construction in JPSS, *Rankin–Selberg Convolutions*
(1983), Section 6.1, printed p.430, formulas (10) and (11). The abstract
character identities, original-carrier coordinates and tensor map are internal
derived content. The module does not assert the image theorem.

For any prime, p-adic field `F` and supplied topological data `T`,
`adjacentRankDeterminantWeight T χ n s` is the smooth character
`χ(det g)|det g|^s`, using the Library's determinant complex power. The base
quasicharacter is arbitrary and continuous. Continuity on the nonarchimedean
GL group gives an open kernel and local constancy of its complex scalar value.
`adjacentRankLower_determinantComplexPower` splits this weight over the actual
diagonal blocks of the ordered lower parabolic `(r+1,1)`.

Write `a(q)` for the large-block projection from `AdjacentRankLowerParabolic`
and `d(q)` for the new explicitly rank-one `adjacentRankLowerScalarProjection`.
`adjacentRankLower_halfModulus` proves the equality of actual unit-valued
characters

`δ̄^(1/2)(q) = |det a(q)|^(-1/2) |det d(q)|^((r+1)/2)`.

Here the left side is exactly `T.oppositeParabolicHalfModulus`, the inverse
positive half of the upper block modulus. The proof starts with the published
two-block modulus `|det a|/|det d|^(r+1)`. Complex powers commute with pullback,
multiplication, inversion and natural powers; the exponent `1/2` is the
Library's positive half-character. Inverting the resulting product proves the
displayed formula, including its sign.

Set `θ(g)=χ(det g)|det g|^((r+1)/2)` on the ambient group and
`ξ(h)=χ(det h)|det h|^((r+2)/2)` on the inner group.
`adjacentRankLower_weightRatio` proves

`θ(q) ξ(a(q))^(-1) = δ̄^(1/2)(q) χ(det d(q))`.

It uses determinant factorization, the preceding half-modulus identity and
addition of determinant exponents. Thus the generic compact-section covariance
is precisely the scalar normalization in JPSS (11).

The remaining constructions use the canonical topological data of `F`. The
original `V : Type uV` is an arbitrary complex module, independently of the
field universe; it has no topology or norm. The exact host block tensor carrier
is `PiTensorProduct ℂ (Shahidi.pairCarrier V (ULift.{uV} ℂ))`.
`adjacentRankLowerTensorCoordinates` identifies it linearly with `V` by the
published pair-to-binary-tensor equivalence, scalar lowering, and the right
unit of tensor product. Its inverse sends `v` to `pairTensor v (ULift.up 1)`.
The block-action theorem proves that these coordinates carry the actual
`σ ⊗ rankOneExtensionCharacter F χ` action to `χ(det d) • σ(a)` on every
vector. It follows first on the displayed inverse image of an arbitrary `v`,
using the factorwise block action, and then on the whole tensor carrier by
surjectivity. No coefficient-model injectivity is used.

`Padic.adjacentRankLowerInducingCoordinates` combines this action identity with
the weight ratio to give an actual representation equivalence between the
host's normalized inducing data and the generic compact-section data. For a
smooth representation `σ`, `Padic.adjacentRankNormalizedSection` postcomposes
the generic compact section with the inverse equivalence. Its codomain is the
actual `F.canonicalNormalizedOppositeParabolicInduced` for the ordered shape
and original host carrier. The test `Φ` belongs to the submodule of rectangular
Schwartz–Bruhat functions whose entire topological support consists of full
row-rank matrices. The measure is exactly `generalLinearHaar F.Carrier r`.
Its finite-on-compacts property justifies the algebraic average, and the
published GL unimodularity theorem supplies right-measure preservation. The
actual identity `[h,0]q=[h a(q),0]` comes from `AdjacentRankLowerParabolic`.

The evaluation theorem gives the literal section value as
`pairTensor (θ(g) • average(Φ,v,g)) (ULift.up 1)`. This average integrates
`Φ([h,0]g) ξ(h) • σ(h⁻¹)v` by the finite algebraic integral, so no integration
of topological `V`-valued functions is assumed. The inherited uniform open
stabilizer makes this an actual smooth induced function.
`Padic.adjacentRankNormalizedSectionTensor` is a linear map on the whole
algebraic tensor product of these compact tests with `V`, obtained by
postcomposition of the generic bilinear construction. Its pure-tensor theorem
is definitional. The right-action theorem is the equality
`ρ(k) section(Φ,v) = θ(k) • section(R_k Φ,v)` of induced vectors, proved by
evaluation and the previously established weighted-average translation law.

Every natural `r`, including zero, is retained. Only smoothness of `σ` is
needed here; irreducibility, Whittaker type and a nonzero coefficient functional
are not hypotheses of this section construction. Surjectivity or spanning by
these sections, the large-twist double-integral identity, construction and
nonvanishing of a common Whittaker functional, and both directions of the
whole image equality remain separate obligations.
