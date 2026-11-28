# Proof of the quantitative compact Dirac limit for real scalar principal series

Module `Langlands.Global.RankinSelberg.RealStandardCompactDiracProof`, namespace
`Langlands.Global.RankinSelbergGlobal.RealStandardCompactDirac`.

`realStandardCompactDirac : RealStandardCompactDiracStatement` proves the statement of the module
`RealStandardCompactDirac` (see `RealStandardCompactDirac.md` for the conventions). The proof
gives the rate `δ = 1`: for `t ≥ 1`,

`‖∫_{O(n)} b_t ξ(k a_t) ψ(k) dk - ψ(1)‖ ≤ C t⁻¹ (‖ψ‖ + L)`.

The helper modules are `RealCompactDiracCorner`, `RealCompactDiracIwasawa`,
`RealCompactDiracTransfer`, `RealCompactDiracSeed`, `RealCompactDiracWeight` and
`RealCompactDiracBigCell` (namespace `Langlands.Global.RankinSelbergGlobal.RealCompactDirac`).

## Auxiliary results of this module

* `isSignCovariant_of_isSignCompatible`: a test `ψ` with `IsSignCompatible ds ψ` satisfies
  `IsSignCovariant (realPositionCharacter ds) ψ`. For `d : Fin n → ℝˣ` take the integer signs
  `εᵢ = sgn dᵢ`; then `signMatrix ε = signDiagonal d` and
  `signCharacter ds ε = ∏ᵢ χᵢ(sgn dᵢ)`.
* `unitHeight_scale_le`: `unitHeight(a_t) ≤ t^{n-1}` for `t ≥ 1` (the row-sum norm of a
  diagonal matrix is the largest absolute value of its entries, Mathlib's
  `Matrix.linfty_opNorm_diagonal`).
* `norm_scaleFactor_pos`, `norm_scaleFactor_inv_le`: `scaleFactor s t ≠ 0` and
  `‖scaleFactor s t‖⁻¹ = ∏ₗ τₗ^{Re s_l} ≤ (t^{n-1})^q ≤ t^{⌈(n-1) q⌉}` for `t ≥ 1`.

## The proof

Let `n = r + 1`, `ds = cs.map RealBlock.character`, `χ = realPositionCharacter ds` and
`e = realPositionExponent ds`. The Library gives `IsSignedPower χ e`
(`RealStrictCharacterLanglandsQuotient.isSignedPower`) and parities `p` with
`χ_l(-1) = (-1)^{p l}` (`RealStrictCharacterLanglandsQuotient.exists_signs`). Let
`s = dualExponent n e` (the exponents `-e_l + (n-1)/2 - l` of the dual principal series) and
`q = growthExponent s`.

1. **Choice of `m`.** `exists_re_integral_weight_pos` gives `M₀`; take
   `m = max(M₀, ⌈1 + (n + 2) q⌉ + 1)`. Then `m ≥ 1`, `1 + (n + 2) q ≤ 2m`, and
   `I = ∫_{O(n)} weight p m s κ dκ` has positive real part, so `I ≠ 0`.
2. **The seed.** `ξ = seedVector p m e`, the extension of the corner-minor profile
   `φ₀ = ∏ₗ (Δₗ Δₗ₊₁)^{p l} (∏ₗ Δₗ)^{2m}`. By `seedVector_mem` it lies in the smooth principal
   series of `χ` and is compact-finite. It is in `realStandardModule n ds` because a list of
   character blocks has no induction blocks (`RealPrincipalSeriesDuality.realInducedBlockAt_map_character`),
   so the Fourier conditions are vacuous.
3. **The data.** `a t = scaleUnits n t` (so `a_t = diag(t^{n-1}, …, 1)` for `t ≥ 1`),
   `b t = (scaleFactor s t · I)⁻¹`, `δ = 1`, `N = max(r, ⌈(n-1) q⌉)` and
   `C = max(1, ‖I‖⁻¹, ‖I‖⁻¹ K)` with `K` from `exists_pointwise_error`. The entries of `a t`
   are positive (`scaleUnits_pos`), `unitHeight(a_t) ≤ t^r ≤ C t^N`, and
   `‖b t‖ = ‖scaleFactor s t‖⁻¹ ‖I‖⁻¹ ≤ t^{⌈(n-1)q⌉} ‖I‖⁻¹ ≤ C t^N`.
4. **The pairing.** By `compactFunction_apply` the Haar pairing is
   `b_t ∫ ξ(k a_t) ψ(k) dk`. The transfer identity `integral_translate_eq` (from the Library's
   `kIntegralInvariance`) rewrites `∫ ξ(k a_t) ψ(k) dk` as `∫ φ₀(k) Ψ(k a_t⁻¹) dk` with
   `Ψ = extension s ψ`, and `ξ = φ₀` on `O(n)` (`seedVector_unitary`).
5. **Normalization.** Since `∫ scaleFactor(s, t) W(k) ψ(1) dk = scaleFactor(s, t) · I · ψ(1)`,

   `b_t ∫ φ₀(k) Ψ(k a_t⁻¹) dk - ψ(1) = b_t ∫ (φ₀(k) Ψ(k a_t⁻¹) - scaleFactor(s, t) W(k) ψ(1)) dk`,

   using that the integrand is continuous and `W` is integrable (`integrable_weight`).
6. **The error.** `exists_pointwise_error` bounds the integrand by
   `‖scaleFactor s t‖ t⁻¹ (‖ψ‖ + L) K`; the measure is a probability measure. Multiplying by
   `‖b t‖ = (‖scaleFactor s t‖ ‖I‖)⁻¹` gives `‖I‖⁻¹ K t⁻¹ (‖ψ‖ + L) ≤ C t^{-1} (‖ψ‖ + L)`.

## How the helper modules enter

* The pointwise error rests on the big-cell computation `bigCell_decomposition`: for `κ` with
  `Q(κ) ≠ 0`, `κ = b L`, and `φ₀(κ) Ψ(κ a_t⁻¹) = scaleFactor(s, t) W(κ) Ψ(Y)` with
  `Y = a_t L a_t⁻¹` and `‖Y - 1‖ ≤ t⁻¹ · n · lowerConstant n / |Q(κ)|`. Then
  `‖Ψ(Y) - ψ(1)‖` is bounded through the Lipschitz bounds for `κ̂` and for the multiplier at the
  identity (`RealCompactDiracIwasawa`) and the Lipschitz constant `L` of `ψ`, and the factor
  `|Q|^{2m}` in `W` absorbs the powers of `|Q|⁻¹` (`exists_pointwise_error`).
* `I ≠ 0` is the Laplace-type argument `exists_re_integral_weight_pos`: near the maximum set of
  `|Q|` on `O(n)` the weight is close to the positive function `|P| Q^{2m}`.

## Relation to the literature

Bernstein–Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, arXiv:0812.1684v3
(Israel J. Math. 199 (2014), 45–111), Appendix A, §12.1.2–§12.1.4, pp. 53–60, prove the spherical
analogue (Theorem 12.2) in the noncompact picture on `N̄`, by the integration formula between
`K` and `N̄`, the scaling `X ↦ a_t X a_t⁻¹` and a near/far splitting. The implemented proof
avoids the integration formula. It moves the translate from the seed to the test function by the
`GL_n(ℝ)`-invariance of the compact pairing, factors `k = b L` on the big cell of `O(n)`, and
applies the scaling to the lower unipotent factor `L`. The near/far splitting is replaced by
the global Lipschitz bounds for the Iwasawa coordinates and the polynomial entry bound
`abs_lower_entry_le`. The seed is the corner-minor seed outlined in step 7 of
`RealStandardCompactDirac.md`.
