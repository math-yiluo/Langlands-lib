# Laurent coefficients of an integral over integer shells

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. Jacquet–Shalika 1985,
in the proof of Corollary (3.3) (printed page 326, used in §4.4 on printed page 329), pass
from the identity of integrals (3.3.3) to the identity of the integrals over each determinant
shell. The tool is the expansion
`Ψ(s) = Σ_m q^(-ms) Ψ^m` (Jacquet, Piatetski-Shapiro and Shalika 1983, (4.2.2), printed
page 407), followed by comparison of coefficients. This module proves that comparison in
abstract form. The variable `X = q^(-s)` is the published `spectralPoint q s`.

- `exists_spectralPoint_eq`: every nonzero `X` equals `q^(-s)` for
  `s = -log X / log q`, and `Re s = -log ‖X‖ / log q`.
- `norm_spectralPoint`: `‖q^(-s)‖ = q^(-Re s)`.
- `integrable_zpow_of_le`: let `D : Q → ℤ` have measurable fibres and let `Φ` vanish where
  `D < j₀`. If `Φ X₀^D` is integrable, so is `Φ X^D` for every nonzero `X` with
  `‖X‖ ≤ ‖X₀‖`. Bound: `|X|^D ≤ (|X|/|X₀|)^(j₀) |X₀|^D` on the support.
- `hasSum_shells`: if `Φ X^D` is integrable, then
  `Σ_j (∫_(D = j) Φ) X^j = ∫ Φ X^D`, by Mathlib's `hasSum_integral_iUnion` for the countable
  partition into fibres.
- `shell_integral_eq_of_const`: assume `Φ` vanishes where `D < j₀`, `Φ (q^(-s₀))^D` is
  integrable for one real `s₀`, and `∫ Φ (q^(-s))^D = K` whenever `Re s > a`. Then
  `∫_(D = j) Φ = K` for `j = 0` and `0` otherwise. Proof: shift indices by
  `j₁ = min j₀ 0` to get a power series. It converges absolutely at a radius
  `r = q^(-s₁) ≤ q^(-s₀)`, `s₁ = max s₀ a + 1`, and on the punctured disc of radius `r` it
  equals the monomial `K X^(-j₁)`, by `exists_spectralPoint_eq`. Then apply
  `coeff_eq_of_tsum_eq_monomial` (PowerSeriesUniqueness).
