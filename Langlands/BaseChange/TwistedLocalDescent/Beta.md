# Replacing an integral over `K` by an integral over an open subgroup

Module `Langlands.BaseChange.TwistedLocalDescent.Beta`. Let `G` be a topological group, `P` and
`K` subgroups with s-finite measures `μP`, `μK` such that `μG = (μP × μK).map (p, k) ↦ p k`, and
`Δ : P → ℝ≥0` the modular factor of `μP`: `μP.map (· * q) = Δ(q) μP`, multiplicative, continuous,
`Δ(1) = 1`. Let `W` be an open subgroup of `G` on which `Δ` is trivial.

- `integral_indicator_mul_modular`: `∫_P 1_W(h h₁) Δ(h) dh = μP(P ∩ W)` for every `h₁ ∈ P`
  (right translation by `h₁⁻¹` and the modular factor cancel).
- `integral_indicator_eq_of_iwasawa` (**β-identity**): let `Φ` be continuous on `G` with
  `Φ(h g) = Δ(h) Φ(g)` for `h ∈ P`, such that every `k ∈ K` with `Φ(k) ≠ 0` lies in `P W x⁻¹`, and
  such that `(p, k) ↦ 1_{W x⁻¹}(p k) Φ(p k)` is integrable. Then
  `μP(P ∩ W) ∫_K Φ = ∫_G 1_{W x⁻¹}(g) Φ(g) dg`.

  Proof: expand the right side with `dg = dp dk` and Fubini; for fixed `k = h₁ w₁ x⁻¹` the inner
  integral is `Φ(k) ∫_P 1_W(h h₁) Δ(h) dh = μP(P ∩ W) Φ(k)`, and it vanishes when `Φ(k) = 0`.
