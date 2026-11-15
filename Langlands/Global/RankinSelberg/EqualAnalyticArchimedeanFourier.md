# Rapid decay of archimedean Fourier transforms for the trace pairing

Module `Langlands.Global.RankinSelberg.EqualAnalyticArchimedeanFourier`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

## Provenance

Internal. The decay of Fourier transforms of Schwartz functions is classical. Here it is derived
from Mathlib's bound for a general continuous bilinear form,
`VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le` (applied with no derivative of
the transform), so no transport to an inner product space is needed.

## Declarations

- `exists_norm_le_sum_of_injective`: an injective linear map `Λ : V → ℝ^ι` on a
  finite-dimensional space satisfies `‖w‖ ≤ K Σ_i |Λ w i|`.
- `one_add_pow_le`: `(1 + x)^N ≤ 2^N (1 + x^N)` for `x ≥ 0`.
- `exists_fourierIntegral_decay`: let `L : V →L V →L ℝ` and let finitely many vectors `v i`
  satisfy `(∀ i, L (v i) w = 0) → w = 0`. Then for every Schwartz `f`, every Haar `μ` and every
  `N` there is `C` with `(1 + ‖w‖)^N ‖𝓕_L f (w)‖ ≤ C`, where
  `𝓕_L f = VectorFourier.fourierIntegral 𝐞 μ L f`. For each `i`, Mathlib bounds
  `|L (v i) w|^N ‖𝓕_L f w‖` by integrals of derivatives of `f`. Choosing the `i` with largest
  `|L (v i) w|` and using the lower bound of the previous lemma gives the claim.
- `traceBilin`, `tracePairing F n β`: the bilinear form `(v, w) ↦ Tr_∞(β Σ_j v_j w_j)` on
  `(F_∞)^n`, where `Tr_∞` is the Library's `mixedTrace`. Lemmas `tracePairing_apply`,
  `neg_tracePairing_toLinearMap₁₂_apply`, `mixedTracePairing_apply`.
- `tracePairing_separates`: if `β β' = 1`, the vectors `Pi.single j (b_k β')` separate points.
  Here `b_k` runs over the lattice basis of the mixed space. The proof uses the Library's
  `mixedTracePairing_injective`.
- `exists_archimedeanFourier_decay`: for a unit `β` of the mixed space and a Schwartz `f` on
  `(F_∞)^n`, `w ↦ ∫ f(v) 𝐞(Tr_∞(β Σ_j v_j w_j)) dv` decays faster than every power of `‖w‖`.
- `continuous_archimedeanFourier`: this transform is continuous (Mathlib
  `VectorFourier.fourierIntegral_continuous`).
