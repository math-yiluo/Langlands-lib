# Representations detected by a test function `1_{I⁺} · ψ(λ_r)` are supercuspidal

Lean module: `Langlands.Representation.AffineGeneric.Supercuspidality`, namespace
`Langlands.AffineGeneric`.

Let `F` be a nonarchimedean local field with uniformizer `ϖ` and residue field `k`, `ψ` a complex
additive character of `k`, `r : Fin (m + 1) → k`, and `f = affineGenericTest ϖ ψ r`, the
function `1_{I⁺} · ψ(λ_r)` of `Langlands.Representation.AffineGeneric.TestFunction`. Give
`GL_{m+1}(F)` a Borel σ-algebra and assume it is Hausdorff, locally compact and totally
disconnected.

## Declarations

- `two_le_length_of_parabolic_ne_top`: a block shape whose parabolic is proper has at least two
  blocks.
- `leftTranslate_affineGenericTest`: for `z ∈ I⁺`, the left translate of `f` by `z`
  (`Hecke.TestFunction.leftTranslate`) is `ψ(λ_r(z⁻¹)) • f`.
- `isSupercuspidal_of_distribution_ne_zero` (**supercuspidality**): if `ψ ≠ 1`, every `rᵢ ≠ 0`,
  `π` is irreducible and admissible, `μ` is a Haar measure and
  `Character.distribution μ π hπ f ≠ 0`, then `GeneralLinear.IsSupercuspidal π`.

**Proof.** The distribution character is the trace of the finite-rank operator `π(f)`
(`Character.distribution_apply`), so `π(f) ≠ 0`; pick `w` with `v = π(f) w ≠ 0`. By
`Hecke.integratedAction_leftTranslate` and `leftTranslate_affineGenericTest`,
`π(z) v = ψ(λ_r(z⁻¹)) v` for every `z ∈ I⁺`. Fix `t` with `ψ(t) ≠ 1`, a proper block shape `B`
and `g`, and let `N = g U_B g⁻¹` (`BlockShape.conjugateUnipotent`). The translates `π(h) v`
span the representation (`span_range_orbit_eq_top`), so by
`coinvariants_subsingleton_of_span` it suffices that each `π(h) v` maps to `0` in the Jacquet
coinvariants for `N`. By `exists_unipotent_affineForm_eq` applied to `h⁻¹ g` there is `u₀ ∈ U_B`
with `z = h⁻¹ g u₀ g⁻¹ h ∈ I⁺` and `λ_r(z) = t`. Then `n = (g u₀ g⁻¹)⁻¹ ∈ N` and
`π(n) π(h) v = π(h) π(z⁻¹) v = ψ(t) π(h) v`. The class of `π(n) π(h) v` equals that of `π(h) v`
(`Jacquet.mk_apply_subgroup`), so `(ψ(t) - 1)` times the class of `π(h) v` is `0`, and the class
is `0` (`Jacquet.mk_eq_zero`).
