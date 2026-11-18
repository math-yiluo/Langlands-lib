# Archimedean regularity of global Whittaker functions

Module `Langlands.Global.RankinSelberg.ArchimedeanWhittakerRegularity`, namespace
`Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity`. Worker 5665 wrote it for
Task 7399. It is the place-independent analytic core of `complexPlaceWhittakerAnalytic`
(module `ComplexPlaceWhittakerAnalyticProof`). It defines auxiliary functions and proves
theorems about them. It states no `Prop` definitions and assumes no premises. Provenance:
internal.

The argument is the usual one: differentiate the Whittaker integral over the compact quotient
`N(F)\N(𝔸)` under the integral sign. Two facts about the vectors of a cuspidal realization
make this work. Their archimedean derivatives are given by the enveloping algebra action, and
they are bounded on every determinant band.

## Setting and notation

* `F` is a number field with compact adele quotient (`CompactSpace (AdeleQuotient F)`), and
  `T : CuspidalOperatorRealization F r` is an actual cuspidal realization of `GL_(r+1)`.
* `cuspFunction F T w : Points F (r + 1) → ℂ` is the cusp function `φ_w` of a vector `w`, and
  `Unfolding.whittaker F r ψ f` is the Whittaker coefficient of `f` for the generic character
  with all coefficients `1` (`cuspWhittaker F T ψ w` is `Unfolding.whittaker F r ψ (φ_w)` by
  definition). `ψ` is a standard additive character (`IsStandardAdditiveCharacter F ψ`).
* `ArchimedeanMatrix F n` are the `n × n` matrices over the mixed space `ℝ^(r₁) × ℂ^(r₂)`, with
  the operator norm. `ArchimedeanGL F n` are their units. `adelicPoint F n g a` is the adelic
  point with archimedean component `g` and finite component `a`, written `(g, a)` below.
* `e = Module.finBasis ℝ (ArchimedeanMatrix F n)`, with coordinate functionals `e*_k`.

## Adelic points and coordinates

* `adelicHomeomorph_adelicPoint`, `detNorm_adelicPoint`, `continuous_detNorm_adelicPoint`:
  the matrix of `(g, a)`, the factorization of its determinant norm, and continuity of
  `g ↦ |det (g, a)|`.
* `archPart x`, `finPart x`: the archimedean component (in matrix coordinates) and the finite
  component of an adelic point `x`.
* `mul_adelicPoint`: `x · (g, b) = (archPart x · g, finPart x · b)`. The proof goes through the
  multiplicative equivalence `adelicEquiv` and `AdelicGL.pair_mul`. Also proved:
  `adelicEquiv_eq_pair`, `adelicEquiv_adelicPoint`, `archPart_adelicPoint`,
  `finPart_adelicPoint`.
* `invCoord k M` is the functional `V ↦ e*_k(M⁻¹ V)`, with `Ring.inverse` (`invCoord_apply`).
  It is smooth on the invertible matrices (`contDiffOn_invCoord`, from
  `contDiffAt_ringInverse`).

## The archimedean slice and its derivative

* `cuspFunction_adelicPoint`, `cuspFunction_mul_adelicPoint`: the values `φ_w((g, b))` and
  `φ_w(x · (g, b))` through the realization (`Unfolding.cuspFunction_apply_eq`).
* `lieDeriv T Z w = R(Z) w` is the action of the enveloping generator
  `Unfolding.matrixGenerator Z` of a real archimedean matrix `Z` on `w`.
  `envelopingValue w y` is the complex-linear map `a ↦ φ_(R(a) w)(y)` on the enveloping
  algebra. Through it, `lieDerivValue w y` (`Z ↦ φ_(R(Z) w)(y)`) is real-linear, and
  `cuspFunction_lieDeriv_eq_sum` expands it in the basis `e`:
  `φ_(R(Z) w)(y) = ∑_k e*_k(Z) φ_(R(e_k) w)(y)`.
* `sliceIntegrand w b x M` is the extension `ArchimedeanGL.coordinateExtension` of the smooth
  archimedean slice of `w` at the finite point `finPart x · b`, evaluated at
  `archPart x · M`. It is defined for every archimedean matrix `M`. At an invertible `g` it is
  `φ_w(x · (g, b))` (`sliceIntegrand_units`).
* `fderiv_coordinateExtension_slice`: the derivative of the slice at `g` in the direction `V`
  is the value of `R(g⁻¹ V) w`. This comes from `Unfolding.smoothDifferential_slice` and
  `ArchimedeanGL.smoothDifferential_apply`.
* `hasFDerivAt_sliceIntegrand`: at an invertible `g` the derivative of
  `M ↦ sliceIntegrand w b x M` is `sliceDeriv w b x g`, which is
  `V ↦ ∑_k φ_(R(e_k) w)(x · (g, b)) · e*_k(g⁻¹ V)`. Proof: the chain rule for
  `M ↦ archPart x · M`, the previous item, the identity
  `(archPart x · g)⁻¹ (archPart x · V) = g⁻¹ V`, and `cuspFunction_lieDeriv_eq_sum`.

## The extended Whittaker function

Let `D` be the Borel fundamental domain of `N(F)` in `N(𝔸)`, `c` the normalizing constant
`quotientMassNormalizer`, and `χ` the generic character with coefficients `1`. Then
`Unfolding.whittaker_eq_setIntegral` gives
`W_f(g) = c · ∫_D f(n g) conj(χ(n)) dn`.

* `archWhittakerExt ψ w b M = c · ∫_D sliceIntegrand w b n M · conj(χ(n)) dn` (Haar measure
  on `N(𝔸)`). At an invertible `g` it is the Whittaker function:
  `archWhittakerExt ψ w b g = W_w((g, b))` (`archWhittakerExt_units`).
* `hasFDerivAt_archWhittakerExt`: at an invertible `g₀`, the derivative is
  `archWhittakerDeriv ψ w b g₀ = ∑_k archWhittakerExt ψ (R(e_k) w) b g₀ · invCoord k g₀`.
  The proof applies `hasFDerivAt_integral_of_dominated_of_fderiv_le` on a neighbourhood `s` of
  `g₀`. `s` consists of the invertible `g` with `d/2 < |det (g, b)| < 2d`, where
  `d = |det (g₀, b)|`, and `‖invCoord k M‖ < ‖invCoord k g₀‖ + 1` for every `k`. Left
  multiplication by `n ∈ N(𝔸)` does not change `|det|` (`detNorm_mul`, `detNorm_unipotent`).
  So on `s` the integrands and their derivatives are bounded by constants, using
  `Unfolding.exists_bound_cuspFunction` for `R(e_k) w` on the band `[d/2, 2d]`. `D` has finite
  measure (`haar_unipotentFundamentalDomain_lt_top`). The integral of the finite sum is then
  rearranged.
* `contDiffOn_archWhittakerExt_nat`, `contDiffOn_archWhittakerExt`: `archWhittakerExt ψ w b`
  is `C^∞` on the invertible matrices. The proof is an induction on the order, for all vectors
  at once, through `contDiffOn_succ_iff_fderiv_of_isOpen`. The derivative is
  `archWhittakerDeriv`: a finite sum of products of extensions for the vectors `R(e_k) w`
  (`C^m` by induction) with the smooth functionals `invCoord k`.
* `integrable_sliceIntegrand` gives integrability at invertible matrices (from
  `Unfolding.integrableOn_whittakerIntegrand`). `archWhittakerExt_lieDeriv_eq_sum` gives
  linearity in `Z` at invertible matrices:
  `archWhittakerExt ψ (R(Z) w) b g = ∑_k e*_k(Z) archWhittakerExt ψ (R(e_k) w) b g`.
* `fderiv_archWhittakerExt_mul`: the derivative at an invertible `g` in the direction `g Z`
  is `archWhittakerExt ψ (R(Z) w) b g`.

## Global determinant bound

`exists_norm_cuspWhittaker_le`: there is a real `β` such that for every standard `ψ` and every
vector `v` there is `C ≥ 0` with `‖W_v(g)‖ ≤ C |det g|^β` for all adelic points `g`. It
follows from the bound for cusp functions
(`CuspCentralBound.exists_norm_cuspFunction_le`) and `Unfolding.norm_whittaker_le`, because
`|det (n g)| = |det g|` for `n ∈ N(𝔸)`.

## Implementation notes

Like the Library modules it builds on (`ExpansionRealization`, `WhittakerDeriv`), the module
uses local `AddCommGroup` instances on the submodule types, a local `LocallyCompactSpace`
instance on `unipotentAdelic`, `open scoped Classical Matrix.Norms.Operator` and
`backward.isDefEq.respectTransparency false`.
