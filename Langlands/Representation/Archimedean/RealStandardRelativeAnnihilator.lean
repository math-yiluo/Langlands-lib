import Langlands.Representation.Archimedean.RealLeviDuality

/-! # Separation by the inverse principal series pairing -/

noncomputable section

open ComplexConjugate MeasureTheory Langlands.LocalFactor.Archimedean
open scoped InnerProductSpace Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealLeviDuality

open PrincipalSeriesAnnihilator RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

/-- The inverse scalar principal series separates every compact-finite vector
outside a compact-stable subspace of the real standard module. -/
def RealStandardRelativeAnnihilatorStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (W : Submodule ℂ (StdSpace n ds)),
    (∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ w ∈ W, realStandardRep n ds k w ∈ W) →
    ∀ v : StdSpace n ds, v ∉ W →
    ∃ u : DualSpace n ds,
      (∀ w ∈ W, ∫ k : unitaryCompact ℝ n, u.val k * w.val k ∂haarK n = 0) ∧
      ∫ k : unitaryCompact ℝ n, u.val k * v.val k ∂haarK n ≠ 0

theorem realStandardRelativeAnnihilator : RealStandardRelativeAnnihilatorStatement := by
  intro n ds W hW v hv
  let χ := realPositionCharacter ds
  let Y : Submodule ℂ (KFin n χ) :=
    (W.map (StdSpace n ds).subtype).comap KFin.toFunLinear
  have hY : IsStable (rho (n := n) (χ := χ)) Y := by
    rintro k x ⟨w, hw, hwx⟩
    refine ⟨realStandardRep n ds ⟨(k.val : Matrix (Fin n) (Fin n) ℝ), k.prop⟩ w,
      hW _ w hw, ?_⟩
    change Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
      (Unitary.toUnits ⟨(k.val : Matrix (Fin n) (Fin n) ℝ), k.prop⟩) w.val =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k.val x.toFun
    rw [toUnits_mk k.val k.prop]
    exact congrArg _ hwx
  have htop : Y ⊔ Yᗮ = ⊤ := by
    by_contra hproper
    have hst : IsStable (rho (n := n) (χ := χ)) (Y ⊔ Yᗮ) := by
      intro k x hx
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add]
      exact Submodule.add_mem_sup (hY k p hp) (isStable_orthogonal rho_isometry hY k q hq)
    obtain ⟨x, hx⟩ : ∃ x : KFin n χ, x ∉ Y ⊔ Yᗮ := by
      by_contra! h
      exact hproper (Submodule.eq_top_iff'.mpr h)
    obtain ⟨u, hu, horth⟩ := exists_ne_zero_inner_eq_zero_kfin (Y ⊔ Yᗮ) hst hx
    have hu' : u ∈ Yᗮ := by
      rw [Submodule.mem_orthogonal']
      exact fun y hy => horth y (Submodule.mem_sup_left hy)
    exact hu (inner_self_eq_zero.mp (horth u (Submodule.mem_sup_right hu')))
  let x := KFin.mk v.val (mem_kFin_of_mem_stdSpace v.prop)
  have hx : x ∈ Y ⊔ Yᗮ := htop ▸ Submodule.mem_top
  have hxY : x ∉ Y := by
    rintro ⟨w, hw, hwx⟩
    have hwv : w = v := Subtype.ext hwx
    exact hv (hwv ▸ hw)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hx
  have hq0 : q ≠ 0 := by
    intro he
    rw [he, add_zero] at hpq
    exact hxY (hpq ▸ hp)
  have hqx : ⟪q, x⟫_ℂ ≠ 0 := by
    rw [← hpq, inner_add_right, Submodule.inner_left_of_mem_orthogonal hp hq, zero_add]
    exact fun e => hq0 (inner_self_eq_zero.mp e)
  obtain ⟨u, hu, huc⟩ := exists_conj_mem_dual
    (RealStrictCharacterLanglandsQuotient.isSignedPower ds) q.toFun_mem
  refine ⟨⟨u, hu⟩, fun w hw => ?_, ?_⟩
  · rw [integral_mul_congr_left _ huc]
    rw [Submodule.mem_orthogonal'] at hq
    have he := hq (KFin.mk w.val (mem_kFin_of_mem_stdSpace w.prop))
      (show KFin.mk w.val (mem_kFin_of_mem_stdSpace w.prop) ∈ Y from ⟨w, hw, rfl⟩)
    rwa [inner_eq] at he
  · rw [integral_mul_congr_left _ huc]
    rwa [inner_eq] at hqx

end Langlands.Archimedean.RealLeviDuality
