import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AlgebraicGeometry.Modules.MorphismVanishing
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-!
# Detecting isomorphisms out of the structure module on a fibre

On a scheme whose global functions form a field, a morphism from the structure module to a
trivial module is either zero or an isomorphism. Hence such a morphism is an isomorphism as
soon as its pullback to some nonempty scheme is an isomorphism.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Picard.FibreFrameLifting

set_option backward.isDefEq.respectTransparency false

/-- The global functions of a smooth proper geometrically connected scheme over a field are
zero or units. -/
theorem eq_zero_or_isUnit_of_smoothProperConnected {κ : CommRingCat.{u}} (hκ : IsField κ)
    {F : Scheme.{u}} (p : F ⟶ Spec κ) [Smooth p] [IsProper p] [GeometricallyConnected p]
    (c : Γ(F, ⊤)) : c = 0 ∨ IsUnit c := by
  have : IsIso p.appTop :=
    smoothProperConnectedGlobalFunctions F (Spec κ) p inferInstance inferInstance
      inferInstance ⊤
  let ρ : Γ(F, ⊤) ≃+* κ :=
    ((asIso p.appTop).symm ≪≫ Scheme.ΓSpecIso κ).commRingCatIsoToRingEquiv
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have hρ : ρ c ≠ 0 := fun h ↦ hc (ρ.injective (h.trans (map_zero ρ).symm))
    obtain ⟨d, hd⟩ := hκ.mul_inv_cancel hρ
    refine isUnit_iff_exists_inv.mpr ⟨ρ.symm d, ρ.injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply, hd, map_one]

/-- On a nonempty scheme the identity of the structure module is not zero. -/
theorem structureModule_id_ne_zero (Y : Scheme.{u}) [Nonempty Y] :
    𝟙 (structureModule Y) ≠ 0 := by
  intro h
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨Classical.arbitrary Y, trivial⟩⟩
  have h₁ : (𝟙 (structureModule Y) : structureModule Y ⟶ structureModule Y).app ⊤
      (1 : Γ(Y, ⊤)) = 0 := by rw [h]; rfl
  exact one_ne_zero (α := Γ(Y, ⊤)) h₁

/-- A morphism from the structure module of `F` to a trivial module is an isomorphism once its
pullback to a nonempty scheme is an isomorphism, provided global functions on `F` are zero or
units. -/
theorem isIso_of_isIso_pullback_map {F F₁ : Scheme.{u}} [Nonempty F₁]
    (hF : ∀ c : Γ(F, ⊤), c = 0 ∨ IsUnit c) {N : F.Modules} (e : N ≅ structureModule F)
    (τ : structureModule F ⟶ N) (h : F₁ ⟶ F)
    (hτ : IsIso ((Scheme.Modules.pullback h).map τ)) : IsIso τ := by
  have hτe : τ = (τ ≫ e.hom) ≫ e.inv := by simp
  rcases hF (structureEndValue (τ ≫ e.hom) ⊤) with hc | hc
  · exfalso
    have h₀ : τ ≫ e.hom = 0 := (structureModule_hom_eq_zero_iff _).mpr hc
    have hτ₀ : τ = 0 := by rw [hτe, h₀, zero_comp]
    have hpull : (Scheme.Modules.pullback h).map τ = 0 := by
      rw [hτ₀, Functor.map_zero]
    obtain ⟨g, hg, -⟩ := hτ
    have hid : 𝟙 ((Scheme.Modules.pullback h).obj (SheafOfModules.unit F.ringCatSheaf)) = 0 :=
      hg.symm.trans (by rw [hpull, zero_comp])
    apply structureModule_id_ne_zero F₁
    have h₁ : (Langlands.Scheme.Modules.pullbackUnitIso h).hom = 0 := by
      rw [← Category.id_comp (Langlands.Scheme.Modules.pullbackUnitIso h).hom, hid, zero_comp]
    have h₂ := (Langlands.Scheme.Modules.pullbackUnitIso h).inv_hom_id
    rw [h₁, comp_zero] at h₂
    exact h₂.symm
  · have hφ : τ ≫ e.hom = (structureAutOfUnit hc.unit).hom :=
      structureEnd_ext (by rw [structureAutOfUnit_hom, structureEndValue_mulHom]; rfl)
    rw [hτe, hφ]
    infer_instance

end Langlands.AlgebraicGeometry.Picard.FibreFrameLifting
