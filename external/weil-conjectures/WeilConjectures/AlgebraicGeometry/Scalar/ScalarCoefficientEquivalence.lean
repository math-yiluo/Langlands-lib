/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement

/-! # Scalar adjunctions under equivalences of coefficient categories

## References

* Stacks Project, Modules on Sites, change of rings
* Stacks, change of rings
* Stacks, Modules on Sites, change of rings
* Stacks, change of rings and adjunction mate calculus
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Identity scalar restriction is identity on sections. -/
def coefficientRestrictIdentity (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules T R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ModuleCat.restrictScalarsId'App _ rfl
        (M.val.obj U)) (fun {_ _} _ ↦ by ext x; rfl)))
    (fun _ ↦ by ext U x; rfl)

/-- The identity restriction comparison after exact localization. -/
def coefficientDerivedRestrictIdentity {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcDerivedRestrict (𝟙 R) ≅ 𝟭 (DerivedCategory (pbcModules T R)) :=
  Functor.mapDerivedCategoryNatIso (coefficientRestrictIdentity T R) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Restriction by an isomorphism of ring sheaves is an equivalence after localization. -/
theorem derivedRestrictIso_isEquivalence {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (b : R ≅ S) :
    (pbcDerivedRestrict b.hom).IsEquivalence := by
  let rS := coefficientRestrictIdentity T S
  let rR := coefficientRestrictIdentity T R
  let eS := pbcDerivedRestrictComp b.inv b.hom (𝟙 S) b.inv_hom_id ≪≫
    Functor.mapDerivedCategoryNatIso rS ≪≫ Functor.mapDerivedCategoryIdIso _
  let eR := pbcDerivedRestrictComp b.hom b.inv (𝟙 R) b.hom_inv_id ≪≫
    Functor.mapDerivedCategoryNatIso rR ≪≫ Functor.mapDerivedCategoryIdIso _
  exact Functor.IsEquivalence.mk' (pbcDerivedRestrict b.inv) eS.symm eR

/-- The exact restriction square of a commutative coefficient square. -/
def derivedRestrictionSquare {T : Scheme.{u}}
    {R₀ R S₀ S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (b : R₀ ⟶ R) (φ : R ⟶ S) (c : S₀ ⟶ S) (ψ : R₀ ⟶ S₀)
    (h : b ≫ φ = ψ ≫ c) :
    pbcDerivedRestrict φ ⋙ pbcDerivedRestrict b ≅
      pbcDerivedRestrict c ⋙ pbcDerivedRestrict ψ :=
  pbcDerivedRestrictComp b φ (b ≫ φ) rfl ≪≫
    (pbcDerivedRestrictComp ψ c (b ≫ φ) h.symm).symm

end AlgebraicGeometry.Scheme

namespace CategoryTheory

/-- A scalar adjunction transports along equivalences with its unit unchanged. -/
theorem scalarAdjunctionCoefficientEquivalence
    {C D C₀ D₀ : Type*} [Category C] [Category D] [Category C₀] [Category D₀]
    {L : C ⥤ D} {R : D ⥤ C} {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
    (a : L ⊣ R) (a₀ : L₀ ⊣ R₀) (U : C ⥤ C₀) (V : D ⥤ D₀)
    [U.IsEquivalence] [V.IsEquivalence] (k : R ⋙ U ≅ V ⋙ R₀) :
    ∃ s : L ⋙ V ≅ U ⋙ L₀,
      ∀ M : C, U.map (a.unit.app M) ≫ k.hom.app (L.obj M) ≫
        R₀.map (s.hom.app M) = a₀.unit.app (U.obj M) := by
  let γ := (mateEquiv a a₀).symm (TwoSquare.mk _ _ _ _ k.hom)
  let aU : U ⊣ U.asEquivalence.inverse := U.asEquivalence.toAdjunction
  let aV : V ⊣ V.asEquivalence.inverse := V.asEquivalence.toAdjunction
  have hm : mateEquiv a a₀ γ = TwoSquare.mk _ _ _ _ k.hom :=
    (mateEquiv a a₀).apply_symm_apply _
  have : IsIso (mateEquiv aV aU (mateEquiv a a₀ γ)) := by
    rw [hm]
    have : IsIso aU.unit := by dsimp only [aU, Equivalence.toAdjunction_unit]; infer_instance
    have : IsIso aV.counit := by
      dsimp only [aV, Equivalence.toAdjunction_counit]
      infer_instance
    simp only [mateEquiv_apply, TwoSquare.mk]
    infer_instance
  have : IsIso (conjugateEquiv (a.comp aV) (aU.comp a₀) γ) := by
    rw [← iterated_mateEquiv_conjugateEquiv a a₀ aU aV γ]
    infer_instance
  have : IsIso γ :=
    conjugateEquiv_of_iso (a.comp aV) (aU.comp a₀) γ
  refine ⟨(asIso γ).symm, ?_⟩
  intro M
  have h := unit_mateEquiv_symm a a₀ (TwoSquare.mk _ _ _ _ k.hom) M
  change U.map (a.unit.app M) ≫ k.hom.app (L.obj M) =
    a₀.unit.app (U.obj M) ≫ R₀.map (γ.app M) at h
  rw [← Category.assoc, h, Category.assoc, ← R₀.map_comp]
  change a₀.unit.app (U.obj M) ≫
    R₀.map ((asIso γ).hom.app M ≫ (asIso γ).inv.app M) = _
  rw [Iso.hom_inv_id_app]
  erw [R₀.map_id, Category.comp_id]

end CategoryTheory
