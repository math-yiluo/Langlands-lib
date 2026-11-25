/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRationalShift
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRationalShift
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Normalized finite-field stages and their coherence

Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.

## References

* Milne, Section 19
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv

namespace CategoryTheory.Functor

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃]

/-- Derived functors of exact functors carry an associative family of composition
isomorphisms to an associative family. -/
theorem mapDerivedCategory_compIso_assoc
    {r₀₁ : C₁ ⥤ C₀} {r₁₂ : C₂ ⥤ C₁} {r₂₃ : C₃ ⥤ C₂} {r₀₂ : C₂ ⥤ C₀} {r₁₃ : C₃ ⥤ C₁}
    {r₀₃ : C₃ ⥤ C₀}
    [r₀₁.Additive] [PreservesFiniteLimits r₀₁] [PreservesFiniteColimits r₀₁]
    [r₁₂.Additive] [PreservesFiniteLimits r₁₂] [PreservesFiniteColimits r₁₂]
    [r₂₃.Additive] [PreservesFiniteLimits r₂₃] [PreservesFiniteColimits r₂₃]
    [r₀₂.Additive] [PreservesFiniteLimits r₀₂] [PreservesFiniteColimits r₀₂]
    [r₁₃.Additive] [PreservesFiniteLimits r₁₃] [PreservesFiniteColimits r₁₃]
    [r₀₃.Additive] [PreservesFiniteLimits r₀₃] [PreservesFiniteColimits r₀₃]
    (c₀₁₂ : r₁₂ ⋙ r₀₁ ≅ r₀₂) (c₁₂₃ : r₂₃ ⋙ r₁₂ ≅ r₁₃) (c₀₂₃ : r₂₃ ⋙ r₀₂ ≅ r₀₃)
    (c₀₁₃ : r₁₃ ⋙ r₀₁ ≅ r₀₃)
    (h : isoWhiskerLeft r₂₃ c₀₁₂ ≪≫ c₀₂₃ =
      (associator _ _ _).symm ≪≫ isoWhiskerRight c₁₂₃ r₀₁ ≪≫ c₀₁₃) :
    isoWhiskerLeft r₂₃.mapDerivedCategory
        ((mapDerivedCategoryCompIso r₁₂ r₀₁) ≪≫ mapDerivedCategoryNatIso c₀₁₂) ≪≫
      ((mapDerivedCategoryCompIso r₂₃ r₀₂) ≪≫ mapDerivedCategoryNatIso c₀₂₃) =
    (associator _ _ _).symm ≪≫
      isoWhiskerRight ((mapDerivedCategoryCompIso r₂₃ r₁₂) ≪≫
        mapDerivedCategoryNatIso c₁₂₃) r₀₁.mapDerivedCategory ≪≫
      ((mapDerivedCategoryCompIso r₁₃ r₀₁) ≪≫ mapDerivedCategoryNatIso c₀₁₃) := by
  ext K
  have hD := congrArg (fun e ↦ (mapDerivedCategoryNatIso e).hom.app K) h
  have hα : (associator r₂₃ r₁₂ r₀₁).symm = Iso.refl _ := by
    ext
    rfl
  simp only [hα, mapDerivedCategoryNatIso_trans, mapDerivedCategoryNatIso_refl,
    NatTrans.comp_app, Category.id_comp] at hD
  have WL := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft r₂₃ c₀₁₂) K
  have WR := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerRight c₁₂₃ r₀₁) K
  have A := NatTrans.congr_app (mapDerivedCategoryCompIso_assoc r₂₃ r₁₂ r₀₁) K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at WL WR A
  have WL' : (mapDerivedCategoryNatIso c₀₁₂).hom.app (r₂₃.mapDerivedCategory.obj K) =
      (mapDerivedCategoryCompIso r₂₃ (r₁₂ ⋙ r₀₁)).hom.app K ≫
        (mapDerivedCategoryNatIso (isoWhiskerLeft r₂₃ c₀₁₂)).hom.app K ≫
        (mapDerivedCategoryCompIso r₂₃ r₀₂).inv.app K := by
    rw [WL, Iso.hom_inv_id_app_assoc]
  have WR' : r₀₁.mapDerivedCategory.map ((mapDerivedCategoryNatIso c₁₂₃).hom.app K) ≫
      (mapDerivedCategoryCompIso r₁₃ r₀₁).hom.app K =
      (mapDerivedCategoryCompIso (r₂₃ ⋙ r₁₂) r₀₁).hom.app K ≫
        (mapDerivedCategoryNatIso (isoWhiskerRight c₁₂₃ r₀₁)).hom.app K := by
    rw [← cancel_mono ((mapDerivedCategoryCompIso r₁₃ r₀₁).inv.app K), Category.assoc,
      Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    rw [WR, Iso.hom_inv_id_app_assoc]
  have A' : (mapDerivedCategoryCompIso r₁₂ r₀₁).hom.app (r₂₃.mapDerivedCategory.obj K) ≫
      (mapDerivedCategoryCompIso r₂₃ (r₁₂ ⋙ r₀₁)).hom.app K =
      r₀₁.mapDerivedCategory.map ((mapDerivedCategoryCompIso r₂₃ r₁₂).hom.app K) ≫
        (mapDerivedCategoryCompIso (r₂₃ ⋙ r₁₂) r₀₁).hom.app K := by
    rw [← cancel_mono ((mapDerivedCategoryCompIso (r₂₃ ⋙ r₁₂) r₀₁).inv.app K),
      Category.assoc, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    rw [← cancel_mono (r₀₁.mapDerivedCategory.map
      ((mapDerivedCategoryCompIso r₂₃ r₁₂).inv.app K)), Category.assoc, Category.assoc, ← A]
    simp [← Functor.map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, isoWhiskerRight_hom, whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [WL', reassoc_of% WR']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp]
  rw [reassoc_of% A', hD]


end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

/-- Pentagon for composition isomorphisms conjugated by normalizations. -/
theorem normalized_comp_assoc
    {R₀₁ T₀₁ : C₀ ⥤ C₁} {R₁₂ T₁₂ : C₁ ⥤ C₂} {R₂₃ T₂₃ : C₂ ⥤ C₃} {R₀₂ T₀₂ : C₀ ⥤ C₂}
    {R₁₃ T₁₃ : C₁ ⥤ C₃} {R₀₃ T₀₃ : C₀ ⥤ C₃} {S₀₂ : C₀ ⥤ C₂} {S₁₃ : C₁ ⥤ C₃}
    {S₀₃ S₀₃' : C₀ ⥤ C₃}
    (N₀₁ : R₀₁ ≅ T₀₁) (N₁₂ : R₁₂ ≅ T₁₂) (N₂₃ : R₂₃ ≅ T₂₃) (N₀₂ : R₀₂ ≅ T₀₂)
    (N₁₃ : R₁₃ ≅ T₁₃) (N₀₃ : R₀₃ ≅ T₀₃)
    (c₀₁₂ : R₀₁ ⋙ R₁₂ ≅ S₀₂) (e₀₁₂ : S₀₂ ≅ R₀₂) (c₁₂₃ : R₁₂ ⋙ R₂₃ ≅ S₁₃) (e₁₂₃ : S₁₃ ≅ R₁₃)
    (c₀₂₃ : R₀₂ ⋙ R₂₃ ≅ S₀₃) (e₀₂₃ : S₀₃ ≅ R₀₃) (c₀₁₃ : R₀₁ ⋙ R₁₃ ≅ S₀₃')
    (e₀₁₃ : S₀₃' ≅ R₀₃)
    (h : ∀ K, R₂₃.map ((c₀₁₂ ≪≫ e₀₁₂).hom.app K) ≫ (c₀₂₃ ≪≫ e₀₂₃).hom.app K =
      (c₁₂₃ ≪≫ e₁₂₃).hom.app (R₀₁.obj K) ≫ (c₀₁₃ ≪≫ e₀₁₃).hom.app K) (K : C₀) :
    T₂₃.map ((isoWhiskerRight N₀₁.symm T₁₂ ≪≫ isoWhiskerLeft R₀₁ N₁₂.symm ≪≫ c₀₁₂ ≪≫ e₀₁₂ ≪≫
        N₀₂).hom.app K) ≫
      (isoWhiskerRight N₀₂.symm T₂₃ ≪≫ isoWhiskerLeft R₀₂ N₂₃.symm ≪≫ c₀₂₃ ≪≫ e₀₂₃ ≪≫
        N₀₃).hom.app K =
    (isoWhiskerRight N₁₂.symm T₂₃ ≪≫ isoWhiskerLeft R₁₂ N₂₃.symm ≪≫ c₁₂₃ ≪≫ e₁₂₃ ≪≫
        N₁₃).hom.app (T₀₁.obj K) ≫
      (isoWhiskerRight N₀₁.symm T₁₃ ≪≫ isoWhiskerLeft R₀₁ N₁₃.symm ≪≫ c₀₁₃ ≪≫ e₀₁₃ ≪≫
        N₀₃).hom.app K := by
  have hK := h K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at hK
  have n₁ := N₂₃.inv.naturality (T₁₂.map (N₀₁.inv.app K) ≫ N₁₂.inv.app (R₀₁.obj K) ≫
    c₀₁₂.hom.app K ≫ e₀₁₂.hom.app K)
  have n₂ := N₂₃.inv.naturality (N₁₂.inv.app (T₀₁.obj K))
  have n₃ := N₁₃.hom.naturality (N₀₁.inv.app K)
  have n₄ := (c₁₂₃ ≪≫ e₁₂₃).hom.naturality (N₀₁.inv.app K)
  have n₅ := N₁₂.inv.naturality (N₀₁.inv.app K)
  simp only [Iso.trans_hom, NatTrans.comp_app, comp_map, Functor.map_comp,
    Category.assoc] at n₁ n₂ n₃ n₄ n₅
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← T₂₃.map_comp_assoc (N₀₂.hom.app K), Iso.hom_inv_id_app, T₂₃.map_id, Category.id_comp,
    ← reassoc_of% n₃, Iso.hom_inv_id_app_assoc, ← reassoc_of% n₄, ← reassoc_of% hK,
    reassoc_of% n₁, reassoc_of% n₂, ← R₂₃.map_comp_assoc (T₁₂.map _), n₅, R₂₃.map_comp_assoc]

/-- Left unit law for composition isomorphisms conjugated by normalizations. -/
theorem normalized_comp_heq_leftUnitor {R₀₀ T₀₀ : C₀ ⥤ C₀} {R₀₁ T₀₁ : C₀ ⥤ C₁} {S : C₀ ⥤ C₁}
    (N₀₀ : R₀₀ ≅ T₀₀) (N₀₁ : R₀₁ ≅ T₀₁) (c : R₀₀ ⋙ R₀₁ ≅ S) (e : S ≅ R₀₁)
    (hT : T₀₀ = 𝟭 C₀) (U : R₀₀ ≅ 𝟭 C₀)
    (hN : ∀ K, N₀₀.hom.app K = U.hom.app K ≫ eqToHom (Functor.congr_obj hT K).symm)
    (p : ∀ K, R₀₁.obj K = R₀₁.obj K)
    (hc : ∀ K, (c ≪≫ e).hom.app K = R₀₁.map (U.hom.app K) ≫ eqToHom (p K)) :
    HEq (isoWhiskerRight N₀₀.symm T₀₁ ≪≫ isoWhiskerLeft R₀₀ N₀₁.symm ≪≫ c ≪≫ e ≪≫ N₀₁)
      (leftUnitor T₀₁) := by
  subst hT
  obtain rfl : N₀₀ = U := by
    ext K
    simpa using hN K
  apply heq_of_eq
  ext K
  have hK := hc K
  have n := N₀₁.inv.naturality (N₀₀.inv.app K)
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToHom_refl, Category.comp_id] at hK
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, leftUnitor_hom_app]
  rw [reassoc_of% hK, reassoc_of% n, ← R₀₁.map_comp_assoc, Iso.inv_hom_id_app]
  erw [R₀₁.map_id, Category.id_comp, Iso.inv_hom_id_app]

/-- Right unit law for composition isomorphisms conjugated by normalizations. -/
theorem normalized_comp_heq_rightUnitor {R₀₁ T₀₁ : C₀ ⥤ C₁} {R₁₁ T₁₁ : C₁ ⥤ C₁} {S : C₀ ⥤ C₁}
    (N₀₁ : R₀₁ ≅ T₀₁) (N₁₁ : R₁₁ ≅ T₁₁) (c : R₀₁ ⋙ R₁₁ ≅ S) (e : S ≅ R₀₁)
    (hT : T₁₁ = 𝟭 C₁) (U : R₁₁ ≅ 𝟭 C₁)
    (hN : ∀ K, N₁₁.hom.app K = U.hom.app K ≫ eqToHom (Functor.congr_obj hT K).symm)
    (p : ∀ K, R₀₁.obj K = R₀₁.obj K)
    (hc : ∀ K, (c ≪≫ e).hom.app K = U.hom.app (R₀₁.obj K) ≫ eqToHom (p K)) :
    HEq (isoWhiskerRight N₀₁.symm T₁₁ ≪≫ isoWhiskerLeft R₀₁ N₁₁.symm ≪≫ c ≪≫ e ≪≫ N₀₁)
      (rightUnitor T₀₁) := by
  subst hT
  obtain rfl : N₁₁ = U := by
    ext K
    simpa using hN K
  apply heq_of_eq
  ext K
  have hK := hc K
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToHom_refl, Category.comp_id] at hK
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, rightUnitor_hom_app]
  rw [reassoc_of% hK, Iso.inv_hom_id_app_assoc]
  erw [Iso.inv_hom_id_app]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

section Ambient
variable {X : Scheme.{u}} {R₀ R₁ R₂ R₃ : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}

theorem pbcRestrictComp_hom_app_val {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ) (M : pbcModules X B)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists φ ψ χ h).exists.choose_spec M U x

theorem pbcRestrictComp_assoc (φ₀₁ : R₀ ⟶ R₁) (φ₁₂ : R₁ ⟶ R₂) (φ₂₃ : R₂ ⟶ R₃)
    (φ₀₂ : R₀ ⟶ R₂) (φ₁₃ : R₁ ⟶ R₃) (φ₀₃ : R₀ ⟶ R₃) (h₀₁₂ : φ₀₁ ≫ φ₁₂ = φ₀₂)
    (h₁₂₃ : φ₁₂ ≫ φ₂₃ = φ₁₃) (h₀₂₃ : φ₀₂ ≫ φ₂₃ = φ₀₃) (h₀₁₃ : φ₀₁ ≫ φ₁₃ = φ₀₃) :
    isoWhiskerLeft (pbcRestrict φ₂₃) (pbcRestrictComp φ₀₁ φ₁₂ φ₀₂ h₀₁₂) ≪≫
        pbcRestrictComp φ₀₂ φ₂₃ φ₀₃ h₀₂₃ =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (pbcRestrictComp φ₁₂ φ₂₃ φ₁₃ h₁₂₃)
        (pbcRestrict φ₀₁) ≪≫ pbcRestrictComp φ₀₁ φ₁₃ φ₀₃ h₀₁₃ := by
  apply Iso.ext
  ext M U x
  change ((pbcRestrictComp φ₀₂ φ₂₃ φ₀₃ h₀₂₃).hom.app M).val.app U
      (((pbcRestrictComp φ₀₁ φ₁₂ φ₀₂ h₀₁₂).hom.app ((pbcRestrict φ₂₃).obj M)).val.app U x) =
    ((pbcRestrictComp φ₀₁ φ₁₃ φ₀₃ h₀₁₃).hom.app M).val.app U
      (((pbcRestrictComp φ₁₂ φ₂₃ φ₁₃ h₁₂₃).hom.app M).val.app U x)
  erw [pbcRestrictComp_hom_app_val, pbcRestrictComp_hom_app_val, pbcRestrictComp_hom_app_val,
    pbcRestrictComp_hom_app_val]

theorem pbcDerivedRestrictComp_assoc (φ₀₁ : R₀ ⟶ R₁) (φ₁₂ : R₁ ⟶ R₂) (φ₂₃ : R₂ ⟶ R₃)
    (φ₀₂ : R₀ ⟶ R₂) (φ₁₃ : R₁ ⟶ R₃) (φ₀₃ : R₀ ⟶ R₃) (h₀₁₂ : φ₀₁ ≫ φ₁₂ = φ₀₂)
    (h₁₂₃ : φ₁₂ ≫ φ₂₃ = φ₁₃) (h₀₂₃ : φ₀₂ ≫ φ₂₃ = φ₀₃) (h₀₁₃ : φ₀₁ ≫ φ₁₃ = φ₀₃) :
    isoWhiskerLeft (pbcDerivedRestrict φ₂₃) (pbcDerivedRestrictComp φ₀₁ φ₁₂ φ₀₂ h₀₁₂) ≪≫
        pbcDerivedRestrictComp φ₀₂ φ₂₃ φ₀₃ h₀₂₃ =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight
        (pbcDerivedRestrictComp φ₁₂ φ₂₃ φ₁₃ h₁₂₃) (pbcDerivedRestrict φ₀₁) ≪≫
        pbcDerivedRestrictComp φ₀₁ φ₁₃ φ₀₃ h₀₁₃ :=
  Functor.mapDerivedCategory_compIso_assoc _ _ _ _
    (pbcRestrictComp_assoc φ₀₁ φ₁₂ φ₂₃ φ₀₂ φ₁₃ φ₀₃ h₀₁₂ h₁₂₃ h₀₂₃ h₀₁₃)

theorem pbcReductionNormalization_hom_eq {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ) (K : DerivedCategory (pbcModules X R)) :
    (pbcReductionNormalization φ ψ χ h K).hom =
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
        (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
        (pbcDerivedRestrictComp φ ψ χ h)).hom.app K := by
  dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [asIso_hom, Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]

theorem pbcReductionNormalization_assoc (φ₀₁ : R₀ ⟶ R₁) (φ₁₂ : R₁ ⟶ R₂) (φ₂₃ : R₂ ⟶ R₃)
    (φ₀₂ : R₀ ⟶ R₂) (φ₁₃ : R₁ ⟶ R₃) (φ₀₃ : R₀ ⟶ R₃) (h₀₁₂ : φ₀₁ ≫ φ₁₂ = φ₀₂)
    (h₁₂₃ : φ₁₂ ≫ φ₂₃ = φ₁₃) (h₀₂₃ : φ₀₂ ≫ φ₂₃ = φ₀₃) (h₀₁₃ : φ₀₁ ≫ φ₁₃ = φ₀₃)
    (K : DerivedCategory (pbcModules X R₀)) :
    (pbcDerivedExtend φ₂₃).map (pbcReductionNormalization φ₀₁ φ₁₂ φ₀₂ h₀₁₂ K).hom ≫
        (pbcReductionNormalization φ₀₂ φ₂₃ φ₀₃ h₀₂₃ K).hom =
      (pbcReductionNormalization φ₁₂ φ₂₃ φ₁₃ h₁₂₃ ((pbcDerivedExtend φ₀₁).obj K)).hom ≫
        (pbcReductionNormalization φ₀₁ φ₁₃ φ₀₃ h₀₁₃ K).hom := by
  have H := congrArg (fun e ↦ e.hom.app K) (Adjunction.leftAdjointCompIso_assoc
    (pbcDerivedScalarAdjunction φ₀₁) (pbcDerivedScalarAdjunction φ₁₂)
    (pbcDerivedScalarAdjunction φ₂₃) (pbcDerivedScalarAdjunction φ₀₂)
    (pbcDerivedScalarAdjunction φ₁₃) (pbcDerivedScalarAdjunction φ₀₃)
    (pbcDerivedRestrictComp φ₀₁ φ₁₂ φ₀₂ h₀₁₂) (pbcDerivedRestrictComp φ₁₂ φ₂₃ φ₁₃ h₁₂₃)
    (pbcDerivedRestrictComp φ₀₁ φ₁₃ φ₀₃ h₀₁₃) (pbcDerivedRestrictComp φ₀₂ φ₂₃ φ₀₃ h₀₂₃)
    (pbcDerivedRestrictComp_assoc φ₀₁ φ₁₂ φ₂₃ φ₀₂ φ₁₃ φ₀₃ h₀₁₂ h₁₂₃ h₀₂₃ h₀₁₃))
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app,
    Category.id_comp] at H
  rw [pbcReductionNormalization_hom_eq, pbcReductionNormalization_hom_eq,
    pbcReductionNormalization_hom_eq, pbcReductionNormalization_hom_eq]
  exact H.symm

theorem _root_.CategoryTheory.Adjunction.leftAdjointIdIso_eq_symm {C : Type*} [Category* C]
    {F G : C ⥤ C} (adj : F ⊣ G) (e : G ≅ 𝟭 C) :
    Adjunction.leftAdjointIdIso adj e =
      ((conjugateIsoEquiv adj Adjunction.id).symm e).symm := by
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id adj).injective
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  exact ((conjugateEquiv Adjunction.id adj).apply_symm_apply e.inv).symm

theorem _root_.CategoryTheory.Functor.mapDerivedCategoryCompIso_whiskerLeft_unit
    {C₀ C₁ : Type*} [Category* C₀] [Category* C₁] [Abelian C₀] [Abelian C₁]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    (r : C₁ ⥤ C₀) (s : C₀ ⥤ C₀) [r.Additive] [PreservesFiniteLimits r]
    [PreservesFiniteColimits r] [s.Additive] [PreservesFiniteLimits s]
    [PreservesFiniteColimits s] (e : s ≅ 𝟭 C₀) (c : r ⋙ s ≅ r)
    (hc : c = isoWhiskerLeft r e ≪≫ rightUnitor r) :
    (mapDerivedCategoryCompIso r s) ≪≫ mapDerivedCategoryNatIso c =
      isoWhiskerLeft r.mapDerivedCategory
        (mapDerivedCategoryNatIso e ≪≫ mapDerivedCategoryIdIso C₀) ≪≫
        rightUnitor r.mapDerivedCategory := by
  subst hc
  have hρ : rightUnitor r = Iso.refl _ := by
    ext
    rfl
  ext K
  have WL := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft r e) K
  have U := NatTrans.congr_app (mapDerivedCategoryCompIso_comp_id r) K
  simp only [NatTrans.comp_app, whiskerLeft_app, NatTrans.id_app] at WL U
  simp only [hρ, mapDerivedCategoryNatIso_trans, mapDerivedCategoryNatIso_refl,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    rightUnitor_hom_app, NatTrans.id_app]
  have WL' : (mapDerivedCategoryNatIso (isoWhiskerLeft r e)).hom.app K =
      (mapDerivedCategoryCompIso r s).inv.app K ≫
        (mapDerivedCategoryNatIso e).hom.app (r.mapDerivedCategory.obj K) ≫
        (mapDerivedCategoryCompIso r (𝟭 C₀)).hom.app K := by
    rw [← reassoc_of% WL, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have U' : (mapDerivedCategoryCompIso r (𝟭 C₀)).hom.app K =
      (mapDerivedCategoryIdIso C₀).hom.app (r.mapDerivedCategory.obj K) := by
    rw [← cancel_epi ((mapDerivedCategoryCompIso r (𝟭 C₀)).inv.app K), Iso.inv_hom_id_app, U]
    rfl
  rw [WL', U']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  all_goals rfl

theorem _root_.CategoryTheory.Functor.mapDerivedCategoryCompIso_whiskerRight_unit
    {C₀ C₁ : Type*} [Category* C₀] [Category* C₁] [Abelian C₀] [Abelian C₁]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    (r : C₁ ⥤ C₀) (s : C₁ ⥤ C₁) [r.Additive] [PreservesFiniteLimits r]
    [PreservesFiniteColimits r] [s.Additive] [PreservesFiniteLimits s]
    [PreservesFiniteColimits s] (e : s ≅ 𝟭 C₁) (c : s ⋙ r ≅ r)
    (hc : c = isoWhiskerRight e r ≪≫ leftUnitor r) :
    (mapDerivedCategoryCompIso s r) ≪≫ mapDerivedCategoryNatIso c =
      isoWhiskerRight (mapDerivedCategoryNatIso e ≪≫ mapDerivedCategoryIdIso C₁)
        r.mapDerivedCategory ≪≫ leftUnitor r.mapDerivedCategory := by
  subst hc
  have hl : leftUnitor r = Iso.refl _ := by
    ext
    rfl
  ext K
  have WR := NatTrans.congr_app (mapDerivedCategoryNatIso_isoWhiskerRight e r) K
  have U := NatTrans.congr_app (mapDerivedCategoryCompIso_id_comp r) K
  simp only [NatTrans.comp_app, whiskerRight_app, NatTrans.id_app] at WR U
  simp only [hl, mapDerivedCategoryNatIso_trans, mapDerivedCategoryNatIso_refl,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    leftUnitor_hom_app, NatTrans.id_app, Functor.map_comp]
  have WR' : (mapDerivedCategoryNatIso (isoWhiskerRight e r)).hom.app K =
      (mapDerivedCategoryCompIso s r).inv.app K ≫
        r.mapDerivedCategory.map ((mapDerivedCategoryNatIso e).hom.app K) ≫
        (mapDerivedCategoryCompIso (𝟭 C₁) r).hom.app K := by
    rw [← reassoc_of% WR, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have U' : (mapDerivedCategoryCompIso (𝟭 C₁) r).hom.app K =
      r.mapDerivedCategory.map ((mapDerivedCategoryIdIso C₁).hom.app K) := by
    rw [← cancel_epi ((mapDerivedCategoryCompIso (𝟭 C₁) r).inv.app K), Iso.inv_hom_id_app, U]
    rfl
  rw [WR', U']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  all_goals rfl


variable {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}

/-- The ordinary-unit-normalized identity extension, conjugate to a restriction unit. -/
abbrev pbcDerivedExtendIdIso (ψ : R ⟶ R) (e : pbcRestrict ψ ≅ 𝟭 _) :
    pbcDerivedExtend (ψ) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (pbcDerivedScalarAdjunction (ψ))
    (Adjunction.id : (𝟭 (DerivedCategory (pbcModules X R))) ⊣ 𝟭 _)).symm
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _)).symm

theorem pbcRestrictComp_id_left (ψ : R ⟶ R) (φ : R ⟶ S) (h : ψ ≫ φ = φ) (e : pbcRestrict ψ ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcRestrictComp (ψ) φ φ h = isoWhiskerLeft (pbcRestrict φ) e ≪≫
      rightUnitor (pbcRestrict φ) := by
  apply Iso.ext
  ext M U x
  change ((pbcRestrictComp (ψ) φ φ h).hom.app M).val.app U x =
    (e.hom.app ((pbcRestrict φ).obj M)).val.app U x
  erw [pbcRestrictComp_hom_app_val, he]

theorem pbcRestrictComp_id_right (φ : R ⟶ S) (ψ : S ⟶ S) (h : φ ≫ ψ = φ) (e : pbcRestrict ψ ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X S) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcRestrictComp φ (ψ) φ h = isoWhiskerRight e (pbcRestrict φ) ≪≫
      leftUnitor (pbcRestrict φ) := by
  apply Iso.ext
  ext M U x
  change ((pbcRestrictComp φ (ψ) φ h).hom.app M).val.app U x =
    (e.hom.app M).val.app U x
  erw [pbcRestrictComp_hom_app_val, he]

theorem pbcDerivedRestrictComp_id_left (ψ : R ⟶ R) (φ : R ⟶ S) (h : ψ ≫ φ = φ)
    (e : pbcRestrict ψ ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcDerivedRestrictComp (ψ) φ φ h = isoWhiskerLeft (pbcDerivedRestrict φ)
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _) ≪≫
        rightUnitor (pbcDerivedRestrict φ) :=
  Functor.mapDerivedCategoryCompIso_whiskerLeft_unit (pbcRestrict φ)
    (pbcRestrict (ψ)) e _ (pbcRestrictComp_id_left ψ φ h e he)

theorem pbcDerivedRestrictComp_id_right (φ : R ⟶ S) (ψ : S ⟶ S) (h : φ ≫ ψ = φ)
    (e : pbcRestrict ψ ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X S) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcDerivedRestrictComp φ (ψ) φ h = isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _)
        (pbcDerivedRestrict φ) ≪≫ leftUnitor (pbcDerivedRestrict φ) :=
  Functor.mapDerivedCategoryCompIso_whiskerRight_unit (pbcRestrict φ)
    (pbcRestrict (ψ)) e _ (pbcRestrictComp_id_right φ ψ h e he)

theorem pbcReductionNormalization_id_left (ψ : R ⟶ R) (φ : R ⟶ S) (h : ψ ≫ φ = φ)
    (e : pbcRestrict ψ ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x)
    (K : DerivedCategory (pbcModules X R)) :
    (pbcReductionNormalization (ψ) φ φ h K).hom =
      (pbcDerivedExtend φ).map ((pbcDerivedExtendIdIso ψ e).hom.app K) := by
  have H := Adjunction.leftAdjointCompIso_id_comp (pbcDerivedScalarAdjunction (ψ))
    (pbcDerivedScalarAdjunction φ) (pbcDerivedRestrictComp (ψ) φ φ h)
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _)
    (pbcDerivedRestrictComp_id_left ψ φ h e he)
  rw [pbcReductionNormalization_hom_eq, H, Adjunction.leftAdjointIdIso_eq_symm]
  simp

theorem pbcReductionNormalization_id_right (φ : R ⟶ S) (ψ : S ⟶ S) (h : φ ≫ ψ = φ)
    (e : pbcRestrict ψ ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X S) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x)
    (K : DerivedCategory (pbcModules X R)) :
    (pbcReductionNormalization φ (ψ) φ h K).hom =
      (pbcDerivedExtendIdIso ψ e).hom.app ((pbcDerivedExtend φ).obj K) := by
  have H := Adjunction.leftAdjointCompIso_comp_id (pbcDerivedScalarAdjunction φ)
    (pbcDerivedScalarAdjunction (ψ)) (pbcDerivedRestrictComp φ (ψ) φ h)
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _)
    (pbcDerivedRestrictComp_id_right φ ψ h e he)
  rw [pbcReductionNormalization_hom_eq, H, Adjunction.leftAdjointIdIso_eq_symm]
  simp


theorem pbcDerivedExtendIdIso_congr (ψ : R ⟶ R) (hψ : ψ = 𝟙 R) (e : pbcRestrict (𝟙 R) ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    (∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      ((eqToIso (congrArg (fun ψ ↦ pbcRestrict ψ) hψ) ≪≫ e).hom.app M).val.app U x = x) ∧
    eqToIso (congrArg (fun ψ ↦ pbcDerivedExtend ψ) hψ) ≪≫ pbcDerivedExtendIdIso _ e =
      pbcDerivedExtendIdIso ψ (eqToIso (congrArg (fun ψ ↦ pbcRestrict ψ) hψ) ≪≫ e) := by
  subst hψ
  rw [eqToIso_refl, eqToIso_refl, Iso.refl_trans, Iso.refl_trans]
  exact ⟨he, rfl⟩

theorem pbcReductionNormalization_congr {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ χ' : R ⟶ B) (h : φ ≫ ψ = χ) (h' : φ ≫ ψ = χ')
    (hχ : χ = χ') (K : DerivedCategory (pbcModules X R)) :
    (pbcReductionNormalization φ ψ χ' h' K).hom =
      (pbcReductionNormalization φ ψ χ h K).hom ≫
        eqToHom (congrArg (fun c ↦ (pbcDerivedExtend c).obj K) hχ) := by
  subst hχ
  rw [eqToHom_refl, Category.comp_id]

end Ambient

section Fields
variable (l : ℕ) [Fact l.Prime]
variable {E F G H : Type u} [Field E] [Field F] [Field G] [Field H]
variable [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) G] [Algebra (Padic l) H]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable [FiniteDimensional (Padic l) G] [FiniteDimensional (Padic l) H]
variable (T : Scheme.{u})

theorem pbcAmbientScalarComp_hom_app (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (pbcAmbientScalarComp l E F G i j T).hom.app K =
      (pbcReductionNormalization (pbcScalarCoefficientMap l E F i T)
        (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
        (pbcScalarCoefficientMap_comp l E F G i j T) K).hom := by
  unfold pbcAmbientScalarComp
  rfl

theorem pbcAmbientScalarComp_assoc (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (k : G →ₐ[Padic l] H) (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l G H k T).map ((pbcAmbientScalarComp l E F G i j T).hom.app K) ≫
        (pbcAmbientScalarComp l E G H (j.comp i) k T).hom.app K =
      (pbcAmbientScalarComp l F G H j k T).hom.app ((pbcEmbeddingAmbientTensor l E F i T).obj K) ≫
        (pbcAmbientScalarComp l E F H i (k.comp j) T).hom.app K ≫
          eqToHom (congrArg (fun a ↦ (pbcEmbeddingAmbientTensor l E H a T).obj K)
            (AlgHom.comp_assoc k j i)) := by
  simp only [pbcAmbientScalarComp_hom_app]
  have h₀₁₃ : pbcScalarCoefficientMap l E F i T ≫ pbcScalarCoefficientMap l F H (k.comp j) T =
      pbcScalarCoefficientMap l E H (k.comp (j.comp i)) T :=
    (pbcScalarCoefficientMap_comp l E F H i (k.comp j) T).trans
      (congrArg (fun a ↦ pbcScalarCoefficientMap l E H a T) (AlgHom.comp_assoc k j i))
  rw [pbcReductionNormalization_assoc _ _ _ _ _ _ _ (pbcScalarCoefficientMap_comp l F G H j k T)
    _ h₀₁₃ K, pbcReductionNormalization_congr _ _ _ _
      (pbcScalarCoefficientMap_comp l E F H i (k.comp j) T) h₀₁₃
      (congrArg (fun a ↦ pbcScalarCoefficientMap l E H a T) (AlgHom.comp_assoc k j i))]

theorem pbcEmbeddingAmbientUnit_eq :
    pbcEmbeddingAmbientUnit l E T =
      eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (pbcScalarCoefficientMap_id l E T)) ≪≫
        pbcDerivedExtendIdIso _ (pbcScalarRestrictId l E T) := by
  rw [pbcEmbeddingAmbientUnit]


theorem pbcScalarRestrictId_hom_app_val
    (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
    (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarRestrictId l E T).hom.app M).val.app U x = x := by
  rw [pbcScalarRestrictId]
  exact (pbcScalarRestrictId_exists l E T).exists.choose_spec M U x

theorem pbcAmbientScalarComp_id_left (i : E →ₐ[Padic l] F)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (pbcAmbientScalarComp l E E F (AlgHom.id (Padic l) E) i T).hom.app K =
      (pbcEmbeddingAmbientTensor l E F i T).map ((pbcEmbeddingAmbientUnit l E T).hom.app K) ≫
        eqToHom (congrArg (fun a ↦ (pbcEmbeddingAmbientTensor l E F a T).obj K)
          (AlgHom.comp_id i).symm) := by
  have h₁ : pbcScalarCoefficientMap l E E (AlgHom.id (Padic l) E) T ≫
      pbcScalarCoefficientMap l E F i T = pbcScalarCoefficientMap l E F i T :=
    (pbcScalarCoefficientMap_comp l E E F (AlgHom.id (Padic l) E) i T).trans
      (congrArg (fun a ↦ pbcScalarCoefficientMap l E F a T) (AlgHom.comp_id i))
  have hc := pbcDerivedExtendIdIso_congr _ (pbcScalarCoefficientMap_id l E T) _
    (pbcScalarRestrictId_hom_app_val l T)
  rw [pbcAmbientScalarComp_hom_app, pbcEmbeddingAmbientUnit_eq, hc.2,
    pbcReductionNormalization_congr _ _ _ _ h₁ _
      (congrArg (fun a ↦ pbcScalarCoefficientMap l E F a T) (AlgHom.comp_id i).symm),
    pbcReductionNormalization_id_left _ _ _ _ hc.1 K]

theorem pbcAmbientScalarComp_id_right (i : E →ₐ[Padic l] F)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (pbcAmbientScalarComp l E F F i (AlgHom.id (Padic l) F) T).hom.app K =
      (pbcEmbeddingAmbientUnit l F T).hom.app ((pbcEmbeddingAmbientTensor l E F i T).obj K) ≫
        eqToHom (congrArg (fun a ↦ (pbcEmbeddingAmbientTensor l E F a T).obj K)
          (AlgHom.id_comp i).symm) := by
  have h₁ : pbcScalarCoefficientMap l E F i T ≫
      pbcScalarCoefficientMap l F F (AlgHom.id (Padic l) F) T =
        pbcScalarCoefficientMap l E F i T :=
    (pbcScalarCoefficientMap_comp l E F F i (AlgHom.id (Padic l) F) T).trans
      (congrArg (fun a ↦ pbcScalarCoefficientMap l E F a T) (AlgHom.id_comp i))
  have hc := pbcDerivedExtendIdIso_congr _ (pbcScalarCoefficientMap_id l F T) _
    (pbcScalarRestrictId_hom_app_val l T)
  rw [pbcAmbientScalarComp_hom_app, pbcEmbeddingAmbientUnit_eq, hc.2,
    pbcReductionNormalization_congr _ _ _ _ h₁ _
      (congrArg (fun a ↦ pbcScalarCoefficientMap l E F a T) (AlgHom.id_comp i).symm),
    pbcReductionNormalization_id_right _ _ _ _ hc.1 K]


variable [IsNoetherian T] [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

theorem pbcRationalScalarComp_hom_app (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarComp l E F G i j T dim.out inv.out).hom.app K =
      (pbcRationalization T (pbcIntegralDatum l G) (pbcUniformizer l G)).map
        (ObjectProperty.homMk ((pbcAmbientScalarComp l E F G i j T).hom.app K.obj.obj)) := by
  unfold pbcRationalScalarComp pbcRationalScalarCompComponent
  rfl

theorem pbcRationalScalarUnit_hom_app
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarUnit l E T dim.out inv.out).hom.app K =
      (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (ObjectProperty.homMk ((pbcEmbeddingAmbientUnit l E T).hom.app K.obj.obj)) := by
  unfold pbcRationalScalarUnit pbcRationalScalarUnitComponent
  rfl

theorem pbcRationalScalarExtension_map_rationalization (i : E →ₐ[Padic l] F)
    {K L : PbcRationalDerivedCategory l E T dim.out inv.out} (f : K.obj ⟶ L.obj) :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).map
        ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f : K ⟶ L) =
      (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        ((pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).map f) := by
  have h := pbcScalarLocalization_naturality l E F i T f
  rw [Category.comp_id, Category.id_comp] at h
  exact h.symm

theorem pbcRationalization_map_homMk_eqToHom {a b : E →ₐ[Padic l] F} (hab : a = b)
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    ((pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        (ObjectProperty.homMk (eqToHom (congrArg
          (fun a ↦ (pbcEmbeddingAmbientTensor l E F a T).obj K.obj.obj) hab))) :
      (pbcRationalScalarExtension l E F a T dim.out inv.out).obj K ⟶
        (pbcRationalScalarExtension l E F b T dim.out inv.out).obj K) =
      eqToHom (congrArg (fun a ↦ (pbcRationalScalarExtension l E F a T dim.out inv.out).obj K)
        hab) := by
  subst hab
  erw [eqToHom_refl, eqToHom_refl]
  exact (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map_id _

theorem pbcRationalScalarComp_assoc (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (k : G →ₐ[Padic l] H) (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarExtension l G H k T dim.out inv.out).map
        ((pbcRationalScalarComp l E F G i j T dim.out inv.out).hom.app K) ≫
        (pbcRationalScalarComp l E G H (j.comp i) k T dim.out inv.out).hom.app K =
      (pbcRationalScalarComp l F G H j k T dim.out inv.out).hom.app
          ((pbcRationalScalarExtension l E F i T dim.out inv.out).obj K) ≫
        (pbcRationalScalarComp l E F H i (k.comp j) T dim.out inv.out).hom.app K ≫
          eqToHom (congrArg (fun a ↦ (pbcRationalScalarExtension l E H a T dim.out inv.out).obj K)
            (AlgHom.comp_assoc k j i)) := by
  rw [pbcRationalScalarComp_hom_app, pbcRationalScalarComp_hom_app,
    pbcRationalScalarComp_hom_app, pbcRationalScalarComp_hom_app]
  erw [pbcRationalScalarExtension_map_rationalization]
  rw [← pbcRationalization_map_homMk_eqToHom l T (AlgHom.comp_assoc k j i)]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  exact pbcAmbientScalarComp_assoc l T i j k K.obj.obj

theorem pbcRationalScalarComp_id_left (i : E →ₐ[Padic l] F)
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarComp l E E F (AlgHom.id (Padic l) E) i T dim.out inv.out).hom.app K =
      (pbcRationalScalarExtension l E F i T dim.out inv.out).map
        ((pbcRationalScalarUnit l E T dim.out inv.out).hom.app K) ≫
        eqToHom (congrArg (fun a ↦ (pbcRationalScalarExtension l E F a T dim.out inv.out).obj K)
          (AlgHom.comp_id i).symm) := by
  rw [pbcRationalScalarComp_hom_app, pbcRationalScalarUnit_hom_app]
  erw [pbcRationalScalarExtension_map_rationalization]
  rw [← pbcRationalization_map_homMk_eqToHom l T (AlgHom.comp_id i).symm]
  erw [← Functor.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  exact pbcAmbientScalarComp_id_left l T i K.obj.obj

theorem pbcAmbientScalarComp_id_right_integral (i : E →ₐ[Padic l] F)
    (η : pbcEmbeddingAmbientTensor l F F (AlgHom.id (Padic l) F) T ⟶ 𝟭 _)
    (hη : ∀ X : PbcCompletedDerived T (pbcIntegralDatum l E),
      (pbcAmbientScalarComp l E F F i (AlgHom.id (Padic l) F) T).hom.app X =
        η.app ((pbcEmbeddingAmbientTensor l E F i T).obj X) ≫
          eqToHom (congrArg (fun a ↦ (pbcEmbeddingAmbientTensor l E F a T).obj X)
            (AlgHom.id_comp i).symm))
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcAmbientScalarComp l E F F i (AlgHom.id (Padic l) F) T).hom.app K.obj.obj =
      η.app ((pbcRationalScalarExtension l E F i T dim.out inv.out).obj K).obj.obj ≫
        eqToHom (congrArg (fun a ↦ (pbcEmbeddingAmbientTensor l E F a T).obj K.obj.obj)
          (AlgHom.id_comp i).symm) :=
  hη K.obj.obj

theorem pbcRationalScalarComp_id_right (i : E →ₐ[Padic l] F)
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarComp l E F F i (AlgHom.id (Padic l) F) T dim.out inv.out).hom.app K =
      (pbcRationalScalarUnit l F T dim.out inv.out).hom.app
          ((pbcRationalScalarExtension l E F i T dim.out inv.out).obj K) ≫
        eqToHom (congrArg (fun a ↦ (pbcRationalScalarExtension l E F a T dim.out inv.out).obj K)
          (AlgHom.id_comp i).symm) := by
  rw [pbcRationalScalarComp_hom_app, pbcRationalScalarUnit_hom_app,
    ← pbcRationalization_map_homMk_eqToHom l T (AlgHom.id_comp i).symm]
  erw [← Functor.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  exact pbcAmbientScalarComp_id_right_integral l T i _ (pbcAmbientScalarComp_id_right l T i) K

theorem pbcRationalScalarComp_unit_left (i b : E →ₐ[Padic l] F)
    (hb : i.comp (AlgHom.id (Padic l) E) = b) (hbi : b = i)
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarComp l E E F (AlgHom.id (Padic l) E) i T dim.out inv.out ≪≫
        eqToIso (congrArg (fun c ↦ pbcRationalScalarExtension l E F c T dim.out inv.out)
          hb)).hom.app K =
      (pbcRationalScalarExtension l E F i T dim.out inv.out).map
          ((pbcRationalScalarUnit l E T dim.out inv.out).hom.app K) ≫
        eqToHom (congrArg (fun c ↦ (pbcRationalScalarExtension l E F c T dim.out inv.out).obj K)
          hbi.symm) := by
  subst hb
  rw [eqToIso_refl, Iso.trans_refl, pbcRationalScalarComp_id_left]

theorem pbcRationalScalarComp_unit_right (i b : E →ₐ[Padic l] F)
    (hb : (AlgHom.id (Padic l) F).comp i = b) (hbi : b = i)
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarComp l E F F i (AlgHom.id (Padic l) F) T dim.out inv.out ≪≫
        eqToIso (congrArg (fun c ↦ pbcRationalScalarExtension l E F c T dim.out inv.out)
          hb)).hom.app K =
      (pbcRationalScalarUnit l F T dim.out inv.out).hom.app
            ((pbcRationalScalarExtension l E F i T dim.out inv.out).obj K) ≫
        eqToHom (congrArg (fun c ↦ (pbcRationalScalarExtension l E F c T dim.out inv.out).obj K)
          hbi.symm) := by
  subst hb
  rw [eqToIso_refl, Iso.trans_refl, pbcRationalScalarComp_id_right]

theorem pbcRationalScalarComp_assoc_of_eq (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (k : G →ₐ[Padic l] H) (ji : E →ₐ[Padic l] G) (kj : F →ₐ[Padic l] H) (kji : E →ₐ[Padic l] H)
    (hji : j.comp i = ji) (hkj : k.comp j = kj) (h₁ : k.comp ji = kji) (h₂ : kj.comp i = kji)
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarExtension l G H k T dim.out inv.out).map
        ((pbcRationalScalarComp l E F G i j T dim.out inv.out ≪≫
          eqToIso (congrArg (fun c ↦ pbcRationalScalarExtension l E G c T dim.out inv.out)
            hji)).hom.app K) ≫
        (pbcRationalScalarComp l E G H ji k T dim.out inv.out ≪≫
          eqToIso (congrArg (fun c ↦ pbcRationalScalarExtension l E H c T dim.out inv.out)
            h₁)).hom.app K =
      (pbcRationalScalarComp l F G H j k T dim.out inv.out ≪≫
          eqToIso (congrArg (fun c ↦ pbcRationalScalarExtension l F H c T dim.out inv.out)
            hkj)).hom.app ((pbcRationalScalarExtension l E F i T dim.out inv.out).obj K) ≫
        (pbcRationalScalarComp l E F H i kj T dim.out inv.out ≪≫
          eqToIso (congrArg (fun c ↦ pbcRationalScalarExtension l E H c T dim.out inv.out)
            h₂)).hom.app K := by
  subst hji
  subst hkj
  subst h₁
  rw [eqToIso_refl, eqToIso_refl, eqToIso_refl, Iso.trans_refl, Iso.trans_refl, Iso.trans_refl,
    pbcRationalScalarComp_assoc, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]


end Fields

section NestedFields
attribute [local irreducible] pbcRationalScalarHom
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
variable (T : Scheme.{u}) [IsNoetherian T]
variable [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The actual finite subfields, in a common ambient field; no algebraic closure
hypothesis is needed for this finite tower. -/
abbrev pbcCoefficientStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcRationalDerivedCategory l E.val T dim.out inv.out

/-- A nested finite subfield inclusion, with its actual algebra homomorphism. -/
def pbcSubfieldInclusion {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    E.val →ₐ[Padic l] F.val := IntermediateField.inclusion h

/-- Identity inclusions are the actual algebra identity. -/
theorem pbcSubfieldInclusion_id (E : Padic.FiniteCoefficientFields l Ω) :
    pbcSubfieldInclusion l Ω (le_refl E) = AlgHom.id (Padic l) E.val := by
  rfl

/-- Actual inclusions compose as direct inclusions. -/
theorem pbcSubfieldInclusion_comp {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    (pbcSubfieldInclusion l Ω h').comp (pbcSubfieldInclusion l Ω h) =
      pbcSubfieldInclusion l Ω (h.trans h') := by
  rfl

/-- The actual rational tensor before literal identity normalization. -/
abbrev pbcStageRaw {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F :=
  pbcRationalScalarExtension l E.val F.val (pbcSubfieldInclusion l Ω h) T dim.out inv.out

/-- Equal coefficient fields use the literal identity functor. -/
def pbcStageTransition {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F := by
  classical
  exact if e : E = F then e ▸ 𝟭 (pbcCoefficientStage l Ω T E)
    else pbcStageRaw l Ω T h

/-- Normalization uses precisely the ordinary tensor multiplication unit. -/
@[irreducible] def pbcStageNormalization {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcStageRaw l Ω T h ≅ pbcStageTransition l Ω T h := by
  classical
  by_cases e : E = F
  · subst F
    exact eqToIso (congrArg
      (fun i ↦ pbcRationalScalarExtension l E.val E.val i T dim.out inv.out)
      (pbcSubfieldInclusion_id l Ω E)) ≪≫
        pbcRationalScalarUnit l E.val T dim.out inv.out ≪≫
          eqToIso (by unfold pbcStageTransition; rw [dite_eq_left rfl])
  · exact eqToIso (by simp only [pbcStageTransition, dite_eq_right e])

/-- Balancing, conjugated by the specified tensor units, is the chosen associator. -/
@[irreducible] def pbcStageAssociator {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    pbcStageTransition l Ω T h ⋙ pbcStageTransition l Ω T h' ≅
      pbcStageTransition l Ω T (h.trans h') :=
  isoWhiskerRight (pbcStageNormalization l Ω T h).symm _ ≪≫
    isoWhiskerLeft _ (pbcStageNormalization l Ω T h').symm ≪≫
    pbcRationalScalarComp l E.val F.val G.val
      (pbcSubfieldInclusion l Ω h) (pbcSubfieldInclusion l Ω h') T dim.out inv.out ≪≫
    eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l E.val G.val i T dim.out inv.out)
      (pbcSubfieldInclusion_comp l Ω h h')) ≪≫
    pbcStageNormalization l Ω T (h.trans h')

/-- Equal coefficient fields use the identity transition. -/
theorem pbcStageTransition_refl (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageTransition l Ω T (le_refl E) = 𝟭 _ := by
  unfold pbcStageTransition
  rw [dite_eq_left rfl]

/-- The normalization at equal fields is the tensor unit. -/
theorem pbcStageNormalization_refl (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageNormalization l Ω T (le_refl E) =
      pbcRationalScalarUnit l E.val T dim.out inv.out ≪≫
        eqToIso (pbcStageTransition_refl l Ω T E).symm := by
  rw [pbcStageNormalization, dite_eq_left rfl]
  exact Iso.refl_trans _

/-- Normalized tensor balancing satisfies both units and the four-field pentagon. -/
theorem pbcStageAssociator_laws :
    (∀ {E F G H : Padic.FiniteCoefficientFields l Ω}
      (h : E ≤ F) (h' : F ≤ G) (h'' : G ≤ H)
      (K : pbcCoefficientStage l Ω T E),
      (pbcStageTransition l Ω T h'').map
          ((pbcStageAssociator l Ω T h h').hom.app K) ≫
        (pbcStageAssociator l Ω T (h.trans h') h'').hom.app K =
      (pbcStageAssociator l Ω T h' h'').hom.app
          ((pbcStageTransition l Ω T h).obj K) ≫
        (pbcStageAssociator l Ω T h (h'.trans h'')).hom.app K) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcStageTransition l Ω T (le_refl E) = 𝟭 _) ∧
    (∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
      HEq (pbcStageAssociator l Ω T (le_refl E) h)
        (Functor.leftUnitor (pbcStageTransition l Ω T h)) ∧
      HEq (pbcStageAssociator l Ω T h (le_refl F))
        (Functor.rightUnitor (pbcStageTransition l Ω T h))) := by
  refine ⟨fun {E F G H} h h' h'' K ↦ ?_, pbcStageTransition_refl l Ω T,
    fun {E F} h ↦ ⟨?_, ?_⟩⟩
  · unfold pbcStageAssociator
    exact Functor.normalized_comp_assoc _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (pbcRationalScalarComp_assoc_of_eq l T _ _ _ _ _ _ (pbcSubfieldInclusion_comp l Ω h h')
        (pbcSubfieldInclusion_comp l Ω h' h'') (pbcSubfieldInclusion_comp l Ω (h.trans h') h'')
        (pbcSubfieldInclusion_comp l Ω h (h'.trans h''))) K
  · unfold pbcStageAssociator
    exact Functor.normalized_comp_heq_leftUnitor _ _ _ _ (pbcStageTransition_refl l Ω T E)
      (pbcRationalScalarUnit l E.val T dim.out inv.out)
      (fun K ↦ by
        rw [pbcStageNormalization_refl]
        simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
        rfl)
      (fun _ ↦ rfl)
      (fun K ↦ pbcRationalScalarComp_unit_left l T _ _
        (pbcSubfieldInclusion_comp l Ω (le_refl E) h) rfl K)
  · unfold pbcStageAssociator
    exact Functor.normalized_comp_heq_rightUnitor _ _ _ _ (pbcStageTransition_refl l Ω T F)
      (pbcRationalScalarUnit l F.val T dim.out inv.out)
      (fun K ↦ by
        rw [pbcStageNormalization_refl]
        simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
        rfl)
      (fun _ ↦ rfl)
      (fun K ↦ pbcRationalScalarComp_unit_right l T _ _
        (pbcSubfieldInclusion_comp l Ω h (le_refl F)) rfl K)

end NestedFields
end AlgebraicGeometry.Scheme
