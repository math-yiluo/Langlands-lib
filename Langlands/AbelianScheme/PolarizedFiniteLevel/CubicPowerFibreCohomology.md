# Cohomology of the powers of the cubic bundle over an algebraically closed field

This module extends the published
`Langlands.AbelianScheme.PolarizedFiniteLevel.cubicFibreCohomology` from the
cubic bundle to all of its positive powers. Let `a` be a datum of relative
dimension `g` and polarization degree `d²` over an algebraically closed
field `K`, and let `k > 0`. Then the `k`-th power of the cubic bundle has no
cohomology in positive degrees, and its global sections have dimension
`(6k)^g * d`.

For `k = 1` this recovers the cohomology computation in the published
`CubicFibreCohomologyStatement`. The module supplies the cohomology calculation
used to identify the Hilbert polynomial `t ↦ 6^g * d * t^g` of a cubic projective
embedding of a fibre. It does not construct such an embedding or prove a
comparison with the geometric fibre invariant of the Hilbert scheme.

## Declarations

`Datum.cubicPowerBundle a k` is the `3k`-th tensor power
`tensorPow a.canonicalBundle.obj (3 * k)` of the datum's diagonal Poincaré
bundle `a.canonicalBundle`. The Library defines `a.cubicBundle` as the third
tensor power of the same bundle. `Datum.cubicPowerBundleIso a k` identifies
the underlying module of `cubicPowerBundle a k` with `tensorPow a.cubicBundle.obj k`
by the inverse of the published `tensorPowMulIso`. The remaining declarations
state their conclusions for `cubicPowerBundle a k`.

`Datum.cubicPowerBundle_isAmple`: over any field and for `k > 0`, the bundle
`cubicPowerBundle a k` is ample. The proof applies the published
`positiveTensorPowerAmple` to the published `Datum.canonicalBundle_isAmple`
with exponent `3k > 0`.

`Datum.cubicPowerBundle_hasFiniteCohomology`: over any field,
`cubicPowerBundle a k` has finite cohomology. This is the first component of
the published `smoothProperLineBundleEulerPolynomial`, applied to
`a.canonicalBundle` at the exponent `3k`.

`Datum.cubicPowerBundleMumford`: over any field, there are normalization data
under which the Mumford map of `cubicPowerBundle a k` equals the parameter
map of `(6k) • a.polarization`. The proof follows the published
`cubicBundleMumford` with exponent `3k` in place of `3`.

1. The published `polarizationDiagonalMumford` shows that the Mumford map of
   `a.canonicalBundle` is the parameter map of `2 • a.polarization`.
2. `LineBundle.exists_tensorObj_iso_structureSheaf` supplies inverse bundles
   and evaluation isomorphisms for `cubicPowerBundle a k` and its
   normalization.
3. The published `isoClass_tensorPow` and
   `mumfordSchemeMapOfLineBundle_eq_pow_of_isoClass` show that the Mumford
   map of `cubicPowerBundle a k` is the `3k`-th power of the Mumford map of
   `a.canonicalBundle`.
4. The published `groupHom_nsmul_hom` identifies that power with the
   parameter map of `(3k) • (2 • a.polarization) = (6k) • a.polarization`.

`Datum.multiplePolarization_degree`: over an algebraically closed field and
for `k > 0`, the morphism `(6k) • a.polarization` is finite and flat, with
constant native rank `(6k)^(2g) * d^2`. The proof follows the published
`Datum.sixfoldPolarization_degree_of_symmetricMultiplication` with `6k` in
place of `6`.

1. The published `multiplication_isIsogeny_finrank_of_symmetricMultiplication`,
   with the symmetric multiplication formula
   `fieldSymmetricMultiplicationPullbackOfCube fieldCubePullback` and the
   ample bundle `a.cubicBundle`, shows that multiplication by `6k` is finite
   and flat of constant native rank `(6k)^(2g)`.
2. The published `groupHom_nsmul_id_eq_multiplication` transports this to
   the endomorphism `(6k) • 𝟙`.
3. The polarization is finite and flat of degree `d^2` (the datum's
   `polarized` and `degree` fields). The composite
   `(6k) • 𝟙 ≫ a.polarization` equals `(6k) • a.polarization`. The published
   `finiteFlatConstantRankComposition` multiplies the ranks.

`Datum.cubicPowerFibreCohomology`: over an algebraically closed field and for
`k > 0`, `H^i(A, cubicPowerBundle a k) = 0` for every `i > 0`, and
`H^0(A, cubicPowerBundle a k)` has `K`-dimension `(6k)^g * d`. The proof
follows the published `cubicFibreCohomology_of_inputs`.

1. Vanishing: the published `ampleLineBundleHigherCohomologyVanishing_of_cube`,
   applied to `fieldCubePullback` and the ample bundle
   `cubicPowerBundle a k`.
2. Using finite cohomology and vanishing, the published
   `finrank_eq_of_higherCohomology_isZero_of_eulerSquare` reduces the
   dimension claim to `χ^2 = ((6k)^g * d)^2` in `ℤ`.
3. The published `algClosedFieldAmpleMumfordEulerSquare`, applied with the
   normalization data of `Datum.cubicPowerBundleMumford` at the image `y` of
   the unit point, gives `χ^2` equal to the native rank of
   `(6k) • a.polarization` at `y`.
4. By `Datum.multiplePolarization_degree`, that rank is
   `(6k)^(2g) * d^2 = ((6k)^g * d)^2`.

The level `n` plays no role, and `0 < d` is not assumed.

## Provenance

This is internal derived content. It composes published Library theorems,
and its route is the one of the published `CubicFibreCohomologyProof` with
the exponent `3` replaced by `3k`. The mathematics is Mumford, Fogarty and
Kirwan, *Geometric Invariant Theory*, third edition, Proposition 6.13 (i)
and (iii) (printed pp.123–124), and Mumford, *Abelian Varieties*, §16
(vanishing theorem and Riemann–Roch `χ(L)^2 = deg φ_L`). The degree
`(6k)^(2g)` of multiplication by `6k` is Milne, *Abelian Varieties*,
Theorem 8.2.
