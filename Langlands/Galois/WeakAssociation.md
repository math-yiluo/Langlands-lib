# Weak association of compatible Galois families with cuspidal spectra

Author: Worker 34. This module defines Harris's *weak association* between a
compatible family of genuine `λ`-adic Galois representations and an
automorphic representation of `GL_n` given by actual cuspidal classes. It only
compares unramified Euler factors at almost all places. It defines no
ramified local compatibility, and it does not assert that any associated
family exists.

## Source

Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134, Section 1, printed pp.183-184: the notion of a
compatible family, the unitary normalization of its partial `L`-function, and
Definition 1.1. Registered original `harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, J. Math. Kyoto Univ. 39, printed p.313, equation (5.6), uses the same
normalized local Artin `L`-function in Theorems 5.7 and 5.9. Registered
original `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

In Harris's text, `ρ = {ρ_λ}` is a compatible family of representations of
`Gal(Ē/E)` on finite-dimensional `L_λ`-spaces, `λ` running over the finite
places of a number field `L`, possibly with finitely many `λ` excluded. There
is a finite set `S` of finite places of `E` such that `ρ_λ` is unramified at
every `v` outside `S` and outside the residue characteristic of `λ`, and the
characteristic polynomials `P_{v,λ}(T) = det(1 - ρ_λ(Frob_v) T)` of a
geometric Frobenius have coefficients in `L` and do not depend on `λ`. The
local factor in the unitary normalization is
`L_v(s, ρ) = ∏_β (1 - (β/|β|) Nv^{-s})^{-1}`, `β` running over the reciprocal
roots of `P_{v,λ}`. Definition 1.1: `ρ` is weakly associated to `π` if
`L^{S'}(s, ρ) = L^{S'}(s, π)` as Euler products for some finite `S' ⊇ S`.

## Library objects used

- `Collection E L excluded`, `MatchesOutside`, `IsCompatible`
  (published `Langlands/Galois/CompatibleFamily`): genuine `λ`-adic
  representations of `Gal(Ē/E)` for the finite places `λ ∉ excluded` of `L`,
  and common Euler polynomials `P_v ∈ L[X]` outside a finite set `S`, at places
  `v` whose residue characteristic differs from that of `λ`. Matching includes
  unramifiedness and uses an actual geometric Frobenius lift; its Euler
  polynomial is `det(1 - ρ_λ(g) T)`.
- `unitaryEulerPolynomial` (published `Langlands/Galois/UnitaryNormalization`):
  `∏ (1 - (β/|β|) T)` over the reciprocal roots `β` of a complex Euler
  polynomial, which is Harris's unitary normalization.
- `SpectralSystem (FinitePlace E) n` and its `eulerPolynomial`
  (published `Langlands/Representation/Unramified/SpectralSystem`): an
  `n`-element multiset of nonzero complex numbers at every place outside a
  finite exceptional set, with Euler polynomial `∏ (1 - α T)`.
- `CuspidalOperatorRealization.IsoClass.HasSpectralSystem` and
  `PositiveRankCuspidalClass.HasSpectralSystem` (published
  `Langlands/Automorphic/CuspidalSpectralPresentation`): the spectral system
  is that of an actual spectral presentation of a representative. Its
  eigenvalues `α` satisfy the normalized spherical Hecke equations, `T_i`
  acting by `q^{i(n-i)/2} e_i(α)` (published
  `Langlands/Representation/Unramified/HeckeOperators`). In this
  normalization `∏ (1 - α Nv^{-s})^{-1}` is the standard local factor
  `L_v(s, π_v)` of the unramified component; the Library does not prove the
  Satake correspondence, and nothing here depends on it.
- `SpectralSystem.finiteSum`: the concatenated spectrum of a finite family,
  whose Euler polynomials are the products of the summands' Euler polynomials.

## Definitions

All names in the first group are in `Langlands.GaloisRepresentation`.

- `UnitaryMatchesSpectrum ι P s`: for all but finitely many places `v` of `E`
  outside the exceptional set of `s`, the unitary normalization of
  `ι(P_v) ∈ ℂ[X]` equals the Euler polynomial of `s` at `v`. This is the
  equality `L^{S'}(s, ρ) = L^{S'}(s, π)` of Euler products.
- `IsWeaklyAssociatedToSpectrum ι excluded R s`: there are a finite set `S`
  and polynomials `P_v ∈ L[X]` with `MatchesOutside excluded R S P` (so `R` is
  compatible with Euler polynomials `P`) and `UnitaryMatchesSpectrum ι P s`.
- `IsSumWeaklyAssociatedToSpectrum ι excluded R s`, for a finite family
  `R k` of collections with common excluded places: one finite set `S` and
  polynomials `P k` with each `R k` matching `P k` outside `S`, and the
  unitary normalization of `∏ₖ P k v` matching `s`. The product is the Euler
  polynomial of the direct sum `⊕ₖ R k` (published
  `eulerPolynomial_directSum`), so this is weak association of the direct
  sum. Harris assumes in practice that the family is a sum of pure families
  (p.183); this definition is the form used for such sums.

In `Langlands.Automorphic`:

- `CuspidalOperatorRealization.IsoClass.IsWeaklyAssociated c ι excluded R`:
  some spectral system `s` of the cuspidal class `c` (rank `r + 1`), attached
  through an actual presentation, has `IsWeaklyAssociatedToSpectrum ι excluded
  R s`.
- `CuspidalOperatorRealization.IsoClass.IsSumWeaklyAssociated c ι excluded R`:
  the same with `IsSumWeaklyAssociatedToSpectrum`.
- `PositiveRankCuspidalClass.IsSpectrumWeaklyAssociated c ι excluded R`, for a
  finite family `c j` of cuspidal classes of ranks `nⱼ`: every `c j` has an
  attached spectral system `s j`, and the direct sum `⊕ₖ R k` is weakly
  associated to `SpectralSystem.finiteSum s`. This is weak association with
  an automorphic representation whose cuspidal spectrum is `(nⱼ, c j)`: at an
  unramified place, the standard Euler factor of such a representation (a
  subquotient of the induced representation from `π₁ ⊗ … ⊗ π_r`) is the
  product of the cuspidal factors (Harris p.184). The Library has no
  isobaric sum construction, so the automorphic side is the family itself.

The universe `uW` in the automorphic definitions is that of the carriers of
the local factors of the witnessing presentations, as in `HasSpectralSystem`.

## Proved properties

- `UnitaryMatchesSpectrum.of_sameEulerPolynomials` and
  `IsWeaklyAssociatedToSpectrum.of_sameEulerPolynomials`: weak association
  depends only on the Euler polynomials of the spectrum outside a finite set.
- `IsWeaklyAssociatedToSpectrum.isCompatible`: a weakly associated
  collection is compatible.
- `isSumWeaklyAssociatedToSpectrum_unique_iff`: for a one-element index type,
  sum weak association is weak association of the single collection.
- `MatchesOutside.ne_zero`: a common Euler polynomial at a matched place is
  nonzero, because the Galois Euler polynomial has constant coefficient one.

## Conventions and boundaries

- The comparison uses one embedding `ι : L → ℂ`, and it depends on `ι`.
  Harris writes `|β|` for "any" complex absolute value: for a pure family the
  normalization radii `|ι(β)|` are the same for every embedding `ι` (p.184,
  "by our purity hypothesis the absolute values `|β|` are well defined").
  The normalized complex polynomial `∏ (1 - (ι(β)/|ι(β)|) T)` itself can
  change with `ι`. For example, a character of order four with coefficient
  field `ℚ(i)` is pure of weight zero; at a place where Frobenius acts by `i`,
  the two embeddings of `ℚ(i)` give the normalized factors `1 - iT` and
  `1 + iT`. Weak association with a fixed automorphic representation is
  therefore a condition on the pair `(R, ι)`, and the statements that use these
  definitions choose `ι` existentially with the family.
- Frobenius is geometric, as in the published `HasEulerPolynomialAt`, and the
  Euler polynomial is `det(1 - ρ_λ(Frob_v) T)` before normalization. No
  arithmetic normalization or half-integral twist is imposed: the unitary
  normalization treats each reciprocal root separately.
- The set of places is cofinite, as in Harris's `S'`; nothing is asserted at
  ramified places or at the places dividing the residue characteristic of
  `λ`.
- Harris's equivalent formulation by unramified Weil-group representations
  (p.184) is not formalized.
