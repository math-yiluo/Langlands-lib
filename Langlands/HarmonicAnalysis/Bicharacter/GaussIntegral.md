# Gauss integrals and Weil's formula

The module `Langlands.HarmonicAnalysis.Bicharacter.GaussIntegral` defines the regularized
integral of a function over a totally disconnected group (its integral over large compact open
subgroups, when it stabilizes) and proves Weil's formula for the Fourier transform of a product
with a character of second degree.

## Content

- `HasGaussIntegral μ f γ`: every compact subset of `X` lies in a compact open subgroup `L` with
  `∫_L f dμ = γ`. For a character of second degree `f`, the integrals over large compact open
  subgroups are eventually constant, and this constant is Weil's integral of `f`.
- `bicharacterFourier_mul_bicharacterFourier` (Weil's formula): let `e` be a self-dual
  bicharacter on `X`, `f`, `g : X → ℂ` and `s : X → X` continuous with
  `f(y) e(y, u) = g(u) f(y + s(u))` for all `y`, `u`, and `HasGaussIntegral μ f γ`. Then for every
  Schwartz–Bruhat function `φ`

  `ℱ (f · ℱ φ) (x) = γ ∫ g(x + z) φ(z) dz`.

  For `f(y) = ψ(½ q(y))` with `q` a non-degenerate quadratic form whose bilinear form is
  `e`-dual to an automorphism `s⁻¹`, the hypothesis is the completion of the square, and the
  formula says that the Fourier transform of `f` is `γ` times `g`, as a distribution. The proof is
  Fubini on `L × supp φ` for a compact open subgroup `L` containing the support of `ℱφ` and the
  points `s(x + z)` for `z` in the support of `φ`, and translation invariance of the integral of
  `f` over `L` (internal lemma `setIntegral_addSubgroup_add_right`).
- `HasGaussIntegral.comp_addEquiv`: if `T : X ≃ₜ+ Y` carries `μ` to `r • μ'` and `f` has Gauss
  integral `γ` for `μ'`, then `f ∘ T` has Gauss integral `r γ` for `μ`.
- `HasGaussIntegral.pi`: a product `x ↦ ∏ᵢ fᵢ(xᵢ)` has Gauss integral `∏ γᵢ` for the product
  measure, if each `fᵢ` has `γᵢ`.

Reference: A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), chapter I,
n° 14, Theorem 2, p. 161, and Corollaries 1 and 2, p. 162 (a non-degenerate character of second
degree `f`, associated with the symmetric isomorphism `ρ` of `G` onto `G*`, has Fourier transform
`x* ↦ γ(f) |ρ|^{-1/2} f(x*ρ⁻¹)⁻¹` with `|γ(f)| = 1`, and `𝓕(Φf) = Φ* ∗ 𝓕(f)`); chapter II, n° 27,
pp. 174–175 (for a non-degenerate quadratic form `f` over a local field with discrete valuation,
`∫_M χ(f(x)) dx` does not depend on the lattice `M` once `M` is large, and `γ(f)` is the argument of
that value). Weil normalizes `γ(f)` to modulus one and proves the stabilization for quadratic forms
on vector spaces; the Library's `γ` is the stabilized integral itself, defined for any function on a
group with compact open subgroups. The Gauss integrals of the norm form of a quadratic extension and
of Hermitian forms, with the Weil indices they produce, are in `Langlands/Theta/WeilIndex/NormForm.lean`
and `Langlands/Theta/DualPair/TensorInvariants.lean`.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/Divisors/UnipVal.lean` lines 39–41
(`HasGauss`); under `Proofs/DivisorProofs/`: `WeilFormulaFourierQuadraticCharacter.lean`,
`HasGaussIntegralCompAddEquivRescale.lean`, `HasGaussIntegralCompactOpenPi.lean` (each whole). The
repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `GlobalTheory.KSp`, `KSp.WeilFormula` → `Langlands.HarmonicAnalysis` and
  `Langlands.HarmonicAnalysis.GaussIntegral.Internal`.
- Renamed: `HasGauss` → `HasGaussIntegral`, `weil_formula` →
  `bicharacterFourier_mul_bicharacterFourier`, `hasGauss_comp_equiv` →
  `HasGaussIntegral.comp_addEquiv`, `hasGauss_pi` → `HasGaussIntegral.pi`.
- `KSp.Good` replaced by Mathlib's classes (`CompactOpenExhaustion` is not needed here);
  `IsPair` → `IsSelfDualBicharacter`; arguments made implicit where they are determined by the
  hypotheses. Types in any universe.

## Declarations

- `HasGaussIntegral`
- `bicharacterFourier_mul_bicharacterFourier`
- `HasGaussIntegral.comp_addEquiv`, `HasGaussIntegral.pi`

All in the namespace `Langlands.HarmonicAnalysis`.

## Dependencies

`Langlands.HarmonicAnalysis.Bicharacter.Fourier`; Mathlib: `MeasureTheory.Constructions.Pi`,
`MeasureTheory.Integral.Pi`.
