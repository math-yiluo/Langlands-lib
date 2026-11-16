# Transpose inverse on `GL_n(F) \ GL_n(𝔸)` and Poisson summation at `g`

Module `Langlands.Global.RankinSelberg.EqualAnalyticDualTransport`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

- **`exists_iota_measurePreserving`**: `ι(g) = ᵗg⁻¹` induces a measure-preserving bijection of
  `GL_n(F) \ GL_n(𝔸)`, sending the class of `g` to that of `ι(g)`. `ι` preserves `GL_n(F)`
  (`iota_rational`), and its Haar character is `1` because `ι` is an involution
  (`mulEquivHaarChar_eq_one_of_involutive`). The quotient statement is the published
  `map_cosetMap_discreteQuotientMeasure`; this argument is the one in `UnequalAnalyticProof`.
- `lift_out_eq`, **`lintegral_out_iota`**, **`integral_out_iota`**: for invariant `f`,
  `∫ f(x.out) = ∫ f(ι(x.out))`, for lower Lebesgue and Bochner integrals.
- `iota_rational_mul_invariant`: `f ∘ ι` is invariant when `f` is.
- `iota_zeta`: `ι(ζ(a)) = ζ(a⁻¹)`. `log_detNorm_iota`: `L(ι g) = -L(g)`.
- **`thetaSum_poisson_points`**: for `Φ ∈ S(𝔸^n)`,
  `Θ(Φ, g) + Φ(0) = e^(-L(g)) (Θ(Φ̂, ι g) + Φ̂(0))` (from `thetaSum_poisson`).

## Provenance

Cogdell 2004, §2.3, printed p.209: the functional equation `E(g, Φ; s, η) = E(ᵗg⁻¹, Φ̂; 1 - s,
η⁻¹)` comes from Poisson summation and the outer automorphism `g ↦ ᵗg⁻¹`. The proofs are
internal.
