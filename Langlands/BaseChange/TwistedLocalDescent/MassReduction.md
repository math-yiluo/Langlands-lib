# Reducing the twisted orbital kernel to the opposite unipotent ball

Module `Langlands.BaseChange.TwistedLocalDescent.MassReduction`.

## The twisted orbital kernel

For a group `G`, a subgroup `P` with a measure `μP`, an endomorphism `θ` of `G`, a set `Q ⊆ P`, a
function `δh` on `P` and a function `φ` on `G`,

`twistedOrbitalKernel θ μP Q δh φ g = ∫_P 1_Q(p) δh(p) φ(g⁻¹ p θ(g)) dp`.

- `twistedOrbitalKernel_mul_right'`: if `φ` is invariant on both sides under a subgroup `V`, the
  kernel is right invariant under `V ∩ θ⁻¹(V)`. `continuous_twistedOrbitalKernel`: for a
  topological group `G`, continuous `θ` and open `V`, this subgroup is open, so the kernel is
  locally constant, hence continuous (`IsClopen.continuous_indicator'` is an auxiliary fact).
- `twistedOrbitalKernel_mul_left`: for `P` locally compact and second countable, if `θ` restricts
  to `θP` on `P`, `Q` is measurable, `Q` and `δh` are invariant under `p ↦ h p θP(h)⁻¹`, `δh` and
  `φ` are continuous, and `μP` is a left Haar measure, then
  `Φ(h g) = Δ_P(θP h) Φ(g)` for `h ∈ P` (left invariance under `h`, then right translation by
  `θP(h)⁻¹`, which scales `μP` by the modular character).

## The reduction

`integral_twistedOrbitalKernel_eq_iwahori`: over an ultrametric proper nontrivially normed field
`𝕂`, let `θ` be continuous with a restriction `θP` to the standard parabolic preserving `μP`,
`μG` a right invariant Haar measure on `GL_n(𝕂)` with `μG = (μP × μK).map (p, k ↦ p k)` for a
compact subgroup `K`, `Q`, `δh` as above (`Q` measurable, `δh` continuous), `φ` continuous and
bi-invariant under an open subgroup, `U` a congruence subgroup of radius `0 < r < 1`, and `x ∈ G`.
If every `k ∈ K` with `Φ(k) ≠ 0` lies in `P U x⁻¹`, then

`∫_K Φ = iwahoriConstant · ∫_{Z ∈ 𝔲̄, ‖Z‖ ≤ r} Φ((1 + Z) x⁻¹) dνL(Z)`.

Proof: the modular character `Δ` of `P` is continuous, trivial on `P ∩ U` and `θP`-invariant
(`ModularCharacter`), so `Φ(h g) = Δ(h) Φ(g)`. The β-identity
(`integral_indicator_eq_of_iwasawa`) gives `μP(P ∩ U) ∫_K Φ = ∫_G 1_{U x⁻¹} Φ`; right invariance
of `μG` turns this into `∫_U Φ(w x⁻¹) dw`; the Iwahori factorization
(`restrict_congruenceBall_eq_map_mul_lowerUnit`) and the left `P ∩ U`-invariance of
`w ↦ Φ(w x⁻¹)` give `iwahoriConstant · μP(P ∩ U) · ∫ Φ((1 + Z) x⁻¹) dνL`; cancel
`μP(P ∩ U) ≠ 0`.
