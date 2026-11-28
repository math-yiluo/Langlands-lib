import Langlands.Algebra.HarishChandra.ParabolicIndependenceStatement

/-! # Transport of a split Cartan subalgebra along a Lie equivalence -/

noncomputable section

set_option autoImplicit false

open LieModule

namespace LieEquiv

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing M] [LieAlgebra ℂ M]
  (e : L ≃ₗ⁅ℂ⁆ M) {H : LieSubalgebra ℂ L} {K : LieSubalgebra ℂ M}
  (hmap : H.map e.toLieHom = K) (χ : K → ℂ)

/-- Transporting an adjoint weight space along a Lie equivalence pulls the weight
back by the equivalence on the acting subalgebras. -/
theorem mem_weightSpace_apply_iff (x : L) :
    e x ∈ weightSpace M χ ↔
      x ∈ weightSpace L (χ ∘ e.ofSubalgebras H K hmap) := by
  let f := e.ofSubalgebras H K hmap
  constructor
  · intro hx
    refine (mem_weightSpace _ _).mpr fun y => e.injective ?_
    change e ⁅(y : L), x⁆ = e (χ (f y) • x)
    rw [map_lie, map_smul]
    have hy := (mem_weightSpace _ _).mp hx (f y)
    change ⁅((f y : K) : M), e x⁆ = χ (f y) • e x at hy
    rw [show (f y : M) = e (y : L) from rfl] at hy
    exact hy
  · intro hx
    refine (mem_weightSpace _ _).mpr fun y => ?_
    obtain ⟨z, rfl⟩ := f.surjective y
    have hz : ⁅(z : L), x⁆ = χ (f z) • x := (mem_weightSpace _ _).mp hx z
    change ⁅((f z : K) : M), e x⁆ = χ (f z) • e x
    simpa only [map_lie, map_smul, f, LieEquiv.ofSubalgebras_apply] using congrArg e hz

/-- The ambient Lie equivalence maps the pulled-back adjoint weight space onto
the adjoint weight space for the given weight. -/
theorem map_weightSpace :
    (weightSpace L (χ ∘ e.ofSubalgebras H K hmap)).toSubmodule.map
      e.toLinearEquiv.toLinearMap = (weightSpace M χ).toSubmodule := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (e.mem_weightSpace_apply_iff hmap χ x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, (e.mem_weightSpace_apply_iff hmap χ x).mp hy, rfl⟩

/-- The linear equivalence of adjoint weight spaces induced by a Lie equivalence
and its restriction to the acting subalgebras. -/
def weightSpaceEquiv :
    weightSpace L (χ ∘ e.ofSubalgebras H K hmap) ≃ₗ[ℂ] weightSpace M χ :=
  e.toLinearEquiv.ofSubmodules _ _ (e.map_weightSpace hmap χ)

end LieEquiv

namespace Langlands.Algebra.HarishChandra

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing M] [LieAlgebra ℂ M]
  {H : LieSubalgebra ℂ L}

/-- The image of a split Cartan subalgebra under a complex Lie equivalence is
split Cartan. -/
theorem IsSplitCartan.map (h : IsSplitCartan H) (e : L ≃ₗ⁅ℂ⁆ M) :
    IsSplitCartan (H.map e.toLieHom) := by
  let K := H.map e.toLieHom
  let f : H ≃ₗ⁅ℂ⁆ K := e.lieSubalgebraMap H
  have hmap (χ : K → ℂ) :
      (weightSpace L (χ ∘ f)).toSubmodule.map e.toLinearEquiv.toLinearMap =
        (weightSpace M χ).toSubmodule :=
    e.map_weightSpace rfl χ
  have pullback_ne_zero (χ : K → ℂ) (hχ : χ ≠ 0) : χ ∘ f ≠ 0 := by
    intro hzero
    apply hχ
    funext y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact congrFun hzero x
  have pullback_ne_bot (χ : K → ℂ) (hχ : weightSpace M χ ≠ ⊥) :
      weightSpace L (χ ∘ f) ≠ ⊥ := by
    intro hbot
    apply hχ
    apply LieSubmodule.toSubmodule_injective
    simp only [← hmap χ, hbot, LieSubmodule.bot_toSubmodule, Submodule.map_bot]
  change IsSplitCartan K
  refine ⟨⟨?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro y z
    obtain ⟨x, rfl⟩ := f.surjective y
    obtain ⟨w, rfl⟩ := f.surjective z
    calc
      ⁅f x, f w⁆ = f ⁅x, w⁆ := (f.map_lie x w).symm
      _ = 0 := by rw [h.isLieAbelian.trivial, map_zero]
  · rw [← LieSubmodule.iSup_toSubmodule_eq_top]
    apply top_unique
    calc
      ⊤ = (⊤ : Submodule ℂ L).map e.toLinearEquiv.toLinearMap := by
        rw [Submodule.map_top]
        exact (LinearMap.range_eq_top.mpr e.surjective).symm
      _ = (⨆ χ : H → ℂ, (weightSpace L χ).toSubmodule).map e.toLinearEquiv.toLinearMap := by
        rw [LieSubmodule.iSup_toSubmodule_eq_top.mpr h.iSup_weightSpace_eq_top]
      _ ≤ ⨆ χ : K → ℂ, (weightSpace M χ).toSubmodule := by
        rw [Submodule.map_iSup]
        refine iSup_le fun ψ => le_iSup_of_le (ψ ∘ f.symm) ?_
        have heq : (ψ ∘ f.symm) ∘ f = ψ := funext fun y =>
          congrArg ψ (f.symm_apply_apply y)
        simpa only [heq] using (hmap (ψ ∘ f.symm)).le
  · have hzero := hmap 0
    change (weightSpace L (0 : H → ℂ)).toSubmodule.map e.toLinearEquiv.toLinearMap =
      (weightSpace M (0 : K → ℂ)).toSubmodule at hzero
    rw [h.weightSpace_zero] at hzero
    exact hzero.symm
  · intro χ hχ hroot
    exact (e.weightSpaceEquiv rfl χ).finrank_eq.symm.trans
      (h.finrank_weightSpace _ (pullback_ne_zero χ hχ) (pullback_ne_bot χ hroot))
  · intro χ hχ hroot
    obtain ⟨x, hx, y, hy, z, hxy, hz⟩ :=
      h.exists_sl2 _ (pullback_ne_zero χ hχ) (pullback_ne_bot χ hroot)
    refine ⟨e x, (e.mem_weightSpace_apply_iff rfl χ x).mpr hx,
      e y, ?_, f z, ?_, hz⟩
    · apply (e.mem_weightSpace_apply_iff rfl (-χ) y).mpr
      exact hy
    · change ⁅e x, e y⁆ = e (z : L)
      rw [← LieEquiv.map_lie, hxy]
  · intro χ hχ hroot c hc hcroot
    exact h.reduced _ (pullback_ne_zero χ hχ) (pullback_ne_bot χ hroot) c hc
      (pullback_ne_bot (c • χ) hcroot)

end Langlands.Algebra.HarishChandra
