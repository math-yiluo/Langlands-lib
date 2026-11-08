# The value of the reduced dual integral when the average is the target

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4: "Then we will get from (9) the simple relation `J_i = c W_(i,0)(e)`",
printed page 329). The canonical topology, valuation and Borel structures are local instances.

- `LastRowReductionLocal.continuous_of_rightInvariant`, `isLocallyConstant_of_rightInvariant`:
  right invariance under an open subgroup gives continuity and local constancy.
- `firstColumnWeight_isLocallyConstant`, `firstColumnWeight_hasCompactSupport`: the weight of
  `DualTarget` is locally constant (by right invariance under the open principal subgroup of
  level `f`) and supported in the compact group `K⁰(f)`.
- `unipotentHaar_firstColumn`: the unipotent elements of `K⁰(f)` are exactly the integral
  unipotent elements, of `unipotentHaar` measure `1` (published `unipotentHaar_integral`).
- `dual_pairing_of_average_eq_target`: let `Ξ` and `F` be functions on `GL_(m+1)`, each right
  invariant under an open subgroup. Suppose `Ξ(g k) = ω(k₀₀)⁻¹ Ξ(g)` for `k ∈ K⁰(f)`,
  `Ξ(u g) = ψN(u)⁻¹ Ξ(g)` and `F(u g) = ψN(u) F(g)` for `u ∈ N`, and that `Ξ F` is integrable on
  `N \ GL_(m+1)`. If the weighted average `F̄ = ∫ w(k) F(· k) dk` equals `c` times the target,
  then `∫ Ξ F = c Ξ(1)`. Proof: by `integral_pair_rightAverage`,
  `∫ Ξ F̄ = μ(K⁰(f)) ∫ Ξ F`. By `integral_out_of_support`, `∫ Ξ (c t) = c ∫_(K⁰(f)) Ξ t = c Ξ(1) μ(K⁰(f))`,
  since `Ξ t ≡ Ξ(1)` on `K⁰(f)`. Finally `μ(K⁰(f))` is positive and finite.

With `Ξ(A) = W_(i,0)(M(diag(A,1)))` (equivariant by `whittaker_dualConj_firstColumn`), this
evaluates the reduced dual integral of `DualReduction` as a multiple of `W_(i,0)(1)` once the
completeness argument has identified the average.
