/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Successive internal scalar mates and normalized units

All functors are the specified ordinary unbounded internal-module functors.
The scalar associator is normalized by its universal computation counits.

## References

* Stacks 0D6D, 0G7E, 07A6
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  HasDerivedCategory.standard

universe u u₀ u₁ u₂ u₃ u₄ u₅ u₆ v₀ v₁ v₂ v₃ v₄ v₅ v₆ w₀ w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
  [MonObj Λ₂] [IsCommMonObj Λ₂]

/-- The canonical comparison for successive exact scalar restrictions. It comes from
ordinary restriction, whose underlying module maps are identities, and localization. -/
def scalarRestrictionComp (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u}) :
    V b T ⋙ V a T ≅ V (a ≫ b) T :=
  (Functor.mapDerivedCategoryCompIso (V₀ b T) (V₀ a T)) ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (coefficientMap a T) (coefficientMap b T)).symm ≪≫
        Mod.comapCongr (coefficientMap_comp a b T).symm)

attribute [local irreducible] scalarRestrictionComp
  scalarAdj Mod.extendRestrictAdjunction CondensedRing.upperStarLowerStarAdjunction
  Functor.leftDerivedFunctorCounit Functor.rightDerivedFunctorUnit

attribute [local irreducible] scalarCounit pullCounit

private theorem conjugate_of_unit {C E : Type*} [Category* C] [Category* E]
    {L L' : C ⥤ E} {R R' : E ⥤ C} (A : L ⊣ R) (B : L' ⊣ R')
    (δ : R ≅ R') (e : L ≅ L')
    (h : ∀ M, A.unit.app M ≫ δ.hom.app (L.obj M) ≫ R'.map (e.hom.app M) =
      B.unit.app M) : conjugateIsoEquiv B A e = δ.symm := by
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit B A e.hom δ.inv
  intro M
  apply (cancel_mono (δ.hom.app (L'.obj M))).1
  rw [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [Category.assoc, δ.hom.naturality]
  exact (h M).symm

private theorem rectangle
    {Y₀ Y₁ Y₂ X₀ X₁ X₂ : Type*}
    [Category Y₀] [Category Y₁] [Category Y₂]
    [Category X₀] [Category X₁] [Category X₂]
    {aY : Y₀ ⥤ Y₁} {bY : Y₁ ⥤ Y₂} {cY : Y₀ ⥤ Y₂}
    {aX : X₀ ⥤ X₁} {bX : X₁ ⥤ X₂} {cX : X₀ ⥤ X₂}
    {rY : Y₁ ⥤ Y₀} {sY : Y₂ ⥤ Y₁} {tY : Y₂ ⥤ Y₀}
    {rX : X₁ ⥤ X₀} {sX : X₂ ⥤ X₁} {tX : X₂ ⥤ X₀}
    {l₀ : Y₀ ⥤ X₀} {l₁ : Y₁ ⥤ X₁} {l₂ : Y₂ ⥤ X₂}
    {f₀ : X₀ ⥤ Y₀} {f₁ : X₁ ⥤ Y₁} {f₂ : X₂ ⥤ Y₂}
    (AY : aY ⊣ rY) (BY : bY ⊣ sY) (CY : cY ⊣ tY)
    (AX : aX ⊣ rX) (BX : bX ⊣ sX) (CX : cX ⊣ tX)
    (A₀ : l₀ ⊣ f₀) (A₁ : l₁ ⊣ f₁) (A₂ : l₂ ⊣ f₂)
    (σY : aY ⋙ bY ≅ cY) (σX : aX ⋙ bX ≅ cX)
    (e₁ : aY ⋙ l₁ ≅ l₀ ⋙ aX) (e₂ : bY ⋙ l₂ ≅ l₁ ⋙ bX)
    (e₃ : cY ⋙ l₂ ≅ l₀ ⋙ cX)
    (δY : sY ⋙ rY ≅ tY) (δX : sX ⋙ rX ≅ tX)
    (r₁ : f₁ ⋙ rY ≅ rX ⋙ f₀) (r₂ : f₂ ⋙ sY ≅ sX ⋙ f₁)
    (r₃ : f₂ ⋙ tY ≅ tX ⋙ f₀)
    (hσY : conjugateIsoEquiv CY (AY.comp BY) σY = δY.symm)
    (hσX : conjugateIsoEquiv CX (AX.comp BX) σX = δX.symm)
    (he₁ : conjugateIsoEquiv (A₀.comp AX) (AY.comp A₁) e₁ = r₁.symm)
    (he₂ : conjugateIsoEquiv (A₁.comp BX) (BY.comp A₂) e₂ = r₂.symm)
    (he₃ : conjugateIsoEquiv (A₀.comp CX) (CY.comp A₂) e₃ = r₃.symm)
    (hr : (Functor.associator sX rX f₀).hom ≫
      (Functor.whiskerLeft sX r₁.inv) ≫
      (Functor.associator sX f₁ rY).inv ≫
      (Functor.whiskerRight r₂.inv rY) ≫
      (Functor.associator f₂ sY rY).hom =
      Functor.whiskerRight δX.hom f₀ ≫ r₃.inv ≫
        Functor.whiskerLeft f₂ δY.inv) :
    (Functor.associator aY bY l₂) ≪≫ isoWhiskerLeft aY e₂ ≪≫
      (Functor.associator aY l₁ bX).symm ≪≫ isoWhiskerRight e₁ bX ≪≫
      (Functor.associator l₀ aX bX) ≪≫ isoWhiskerLeft l₀ σX =
      isoWhiskerRight σY l₂ ≪≫ e₃ := by
  apply (conjugateIsoEquiv (A₀.comp CX) ((AY.comp BY).comp A₂)).injective
  conv_lhs => rw [← Iso.trans_assoc, ← Iso.trans_assoc, ← Iso.trans_assoc,
    ← Iso.trans_assoc]
  rw [conjugateIsoEquiv_trans _ (A₀.comp (AX.comp BX))]
  rw [conjugateIsoEquiv_trans _ ((A₀.comp AX).comp BX)]
  rw [conjugateIsoEquiv_trans _ ((AY.comp A₁).comp BX)]
  rw [conjugateIsoEquiv_trans _ (AY.comp (A₁.comp BX))]
  rw [conjugateIsoEquiv_trans _ (AY.comp (BY.comp A₂))]
  rw [conjugateIsoEquiv_trans _ (CY.comp A₂)]
  rw [conjugateIsoEquiv_isoWhiskerLeft CX (AX.comp BX) A₀ σX,
    conjugateIsoEquiv_associator A₀ AX BX,
    conjugateIsoEquiv_isoWhiskerRight (A₀.comp AX) (AY.comp A₁) BX e₁,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator AY A₁ BX,
    conjugateIsoEquiv_isoWhiskerLeft (A₁.comp BX) (BY.comp A₂) AY e₂,
    conjugateIsoEquiv_associator AY BY A₂,
    conjugateIsoEquiv_isoWhiskerRight CY (AY.comp BY) A₂ σY,
    hσY, hσX, he₁, he₂, he₃]
  apply Iso.ext
  dsimp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom]
  rw [hr]
  simp only [← Functor.whiskerRight_comp_assoc, Iso.inv_hom_id,
    Functor.whiskerRight_id', Category.id_comp]

private theorem unit_transport
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    {F : A ⥤ B} {R : B ⥤ A} {FD : DA ⥤ DB} {RF RD : DB ⥤ DA}
    (a : F ⊣ R) (ad : FD ⊣ RF) (QA : A ⥤ DA) (QB : B ⥤ DB)
    (ε : QA ⋙ FD ⟶ F ⋙ QB) (η : R ⋙ QA ⟶ QB ⋙ RF)
    (χ : RF ≅ RD) (ρ : QB ⋙ RD ≅ R ⋙ QA)
    (hf : ∀ P, ad.unit.app (QA.obj P) ≫ RF.map (ε.app P) =
      QA.map (a.unit.app P) ≫ η.app (F.obj P))
    (hr : ∀ H, η.app H ≫ χ.hom.app (QB.obj H) ≫ ρ.hom.app H = 𝟙 _) (P : A) :
    (ad.ofNatIsoRight χ).unit.app (QA.obj P) ≫
      RD.map (ε.app P) ≫ ρ.hom.app (F.obj P) = QA.map (a.unit.app P) := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, whiskerLeft_app]
  rw [Category.assoc, ← χ.hom.naturality_assoc, ← Category.assoc, hf]
  simp only [Category.assoc, Functor.comp_obj]
  rw [hr]
  exact Category.comp_id _

private def rawAdj (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}} [MonObj R] [MonObj S] [IsCommMonObj R]
    (a : R ⟶ S) [IsMonHom a] : Mod.extendScalars a ⊣ Mod.comap a := by
  let C := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  let hl : ∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z) :=
    ProEtale.preservesColimitsOfSize_tensorLeft_sheaf Ab.{u + 1} T
  let hr : ∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z) :=
    ProEtale.preservesColimitsOfSize_tensorRight_sheaf Ab.{u + 1} T
  exact @Mod.extendRestrictAdjunction.{u + 1, u + 2} C _ _ _ hl hr _ R S _ _ _ a _

private def ordinaryAdj (a : Λ₀ ⟶ Λ₁) [IsMonHom a] (T : Scheme.{u}) :
    extension a T ⊣ V₀ a T := rawAdj T (coefficientMap a T)

section GeneralDerived

variable {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions E]

private theorem derived_unit_exact_right
    (U : C ⥤ E) (R : E ⥤ C) [U.Additive] [R.Additive] [U.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (A : U ⊣ R) (P : HomotopyCategory C (.up ℤ)) :
    (A.derivedAdjunction.ofNatIsoRight R.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Qh.obj P) ≫
      R.mapDerivedCategory.map (U.leftDerivedFunctorCounit.app P) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((U.mapHomotopyCategory (.up ℤ)).obj P) =
    DerivedCategory.Qh.map ((A.mapHomotopyCategory (.up ℤ)).unit.app P) := by
  have hf := (A.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) U.leftDerivedFunctorCounit
    R.rightDerivedFunctorUnit
  have hr : ∀ H : HomotopyCategory E (.up ℤ),
      R.rightDerivedFunctorUnit.app H ≫
      R.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj H) ≫
      R.mapDerivedCategoryFactorsh.hom.app H = 𝟙 _ := by
    intro H
    have h := NatTrans.congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac H
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    rw [← Category.assoc, h, Iso.inv_hom_id_app]
  exact unit_transport (A.mapHomotopyCategory (.up ℤ)) A.derivedAdjunction
    DerivedCategory.Qh DerivedCategory.Qh U.leftDerivedFunctorCounit
    R.rightDerivedFunctorUnit R.rightDerivedFunctorIsoMapDerivedCategory
    R.mapDerivedCategoryFactorsh hf hr P

omit [Abelian.HasKInjectiveResolutions E] in
private theorem derived_post_ext
    (U : C ⥤ E) [U.Additive] [U.PreservesKFlatQuasiIso]
    {B : Type*} [Category* B] (H : DerivedCategory E ⥤ B)
    {G : DerivedCategory C ⥤ B} (α β : G ⟶ U.leftDerivedFunctor ⋙ H)
    (h : ∀ P : HomotopyCategory C (.up ℤ),
      α.app (DerivedCategory.Qh.obj P) ≫ H.map (U.leftDerivedFunctorCounit.app P) =
        β.app (DerivedCategory.Qh.obj P) ≫ H.map (U.leftDerivedFunctorCounit.app P)) :
    α = β := by
  classical
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let Q : HomotopyCategory C (.up ℤ) ⥤ DerivedCategory C := DerivedCategory.Qh
  have : Q.EssSurj := Localization.essSurj Q W
  ext K
  let R : W.localizerMorphismKFlat.LeftResolution (Q.objPreimage K) :=
    Classical.arbitrary _
  have hR : IsIso (Q.map R.w) := Localization.inverts Q W R.w R.hw
  let e : Q.obj R.X₁.obj ≅ K := asIso (Q.map R.w) ≪≫ Q.objObjPreimageIso K
  have hε : IsIso (U.leftDerivedFunctorCounit.app R.X₁.obj) :=
    U.derives_kFlat.isIso_of_isLeftDerivedFunctor U.leftDerivedFunctorCounit R.X₁
  have hh : α.app (Q.obj R.X₁.obj) = β.app (Q.obj R.X₁.obj) :=
    (cancel_mono (H.map (U.leftDerivedFunctorCounit.app R.X₁.obj))).1 (h R.X₁.obj)
  apply (cancel_epi (G.map e.hom)).1
  rw [α.naturality, β.naturality, hh]

end GeneralDerived

private theorem module_derived_unit
    {C : Type u₀} [Category.{v₀} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [IsGrothendieckAbelian.{v₀} C] [Abelian.HasFunctorialFlatResolution C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    (P : HomotopyCategory (Mod C R) (.up ℤ)) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction a).unit.app (DerivedCategory.Qh.obj P) ≫
      (Mod.comap a).mapDerivedCategory.map ((Mod.extendScalars a).leftDerivedFunctorCounit.app P) ≫
      (Mod.comap a).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars a).mapHomotopyCategory (.up ℤ)).obj P) =
      DerivedCategory.Qh.map
        (((Mod.extendRestrictAdjunction a).mapHomotopyCategory (.up ℤ)).unit.app P) := by
  have h := derived_unit_exact_right (Mod.extendScalars a) (Mod.comap a)
    (Mod.extendRestrictAdjunction a) P
  dsimp only [Mod.derivedExtendMapDerivedCategoryAdjunction,
    Mod.derivedExtendRestrictAdjunction, Mod.rightDerivedComapIsoMapDerivedCategory]
  exact h

private theorem scalar_unit_computation (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (T : Scheme.{u}) (P : HomotopyCategory (Modules Λ₀ T) (.up ℤ)) :
    (scalarAdj a T).unit.app (DerivedCategory.Qh.{u + 1, u + 1, u + 2}.obj P) ≫
        (V a T).map ((scalarCounit a T).app P) ≫
        (Functor.mapDerivedCategoryFactorsh.{u + 1, u + 1} (V₀ a T)).hom.app
          (((extension a T).mapHomotopyCategory (.up ℤ)).obj P) =
      (DerivedCategory.Qh (C := Modules Λ₀ T)).map
        (((ordinaryAdj a T).mapHomotopyCategory
          (.up ℤ)).unit.app P) := by
  unfold scalarAdj scalarCounit D V ordinaryAdj rawAdj
  exact module_derived_unit (coefficientMap a T) P

private theorem scalar_hom_comparison (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (T : Scheme.{u}) (P : HomotopyCategory (Modules Λ₀ T) (.up ℤ))
    (H : HomotopyCategory (Modules Λ₁ T) (.up ℤ))
    (g : ((extension a T).mapHomotopyCategory (.up ℤ)).obj P ⟶ H) :
    (scalarAdj a T).homEquiv _ _ ((scalarCounit a T).app P ≫
      DerivedCategory.Qh.map g) =
    DerivedCategory.Qh.map (((ordinaryAdj a T).mapHomotopyCategory (.up ℤ)).homEquiv
      P H g) ≫ (V₀ a T).mapDerivedCategoryFactorsh.inv.app H := by
  apply (cancel_mono ((V₀ a T).mapDerivedCategoryFactorsh.hom.app H)).1
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app]
  have hn := (V₀ a T).mapDerivedCategoryFactorsh.hom.naturality g
  change (V a T).map (DerivedCategory.Qh.map g) ≫
      (V₀ a T).mapDerivedCategoryFactorsh.hom.app H =
    (V₀ a T).mapDerivedCategoryFactorsh.hom.app _ ≫
      DerivedCategory.Qh.map (((V₀ a T).mapHomotopyCategory (.up ℤ)).map g) at hn
  rw [hn]
  erw [Category.comp_id]
  simpa only [V, V₀, Category.assoc] using congrArg
    (fun z ↦ z ≫ DerivedCategory.Qh.map
      (((V₀ a T).mapHomotopyCategory (.up ℤ)).map g))
    (scalar_unit_computation a T P)

attribute [local irreducible] ordinaryAdj rawAdj ordinaryComp

private def resOrd (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u}) :
    V₀ b T ⋙ V₀ a T ≅ V₀ (a ≫ b) T :=
  (Mod.comapComp (coefficientMap a T) (coefficientMap b T)).symm ≪≫
    Mod.comapCongr (coefficientMap_comp a b T).symm

private theorem uniqueness_transport_unit {C E : Type*} [Category* C] [Category* E]
    {F F₀ F₁ : C ⥤ E} {G G₁ : E ⥤ C}
    (A : F ⊣ G) (B : F₀ ⊣ G) (H : F₁ ⊣ G₁) (e : G ≅ G₁) (M : C) :
    A.unit.app M ≫ e.hom.app (F.obj M) ≫
      G₁.map ((A.leftAdjointUniq B).hom.app M ≫
        (B.leftAdjointUniq (H.ofNatIsoRight e.symm)).hom.app M) = H.unit.app M := by
  rw [Functor.map_comp, ← e.hom.naturality_assoc, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]
  rw [← e.hom.naturality, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem module_composition_unit
    {C : Type u₀} [Category.{v₀} C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
    [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
    {R S T : C} [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (b : S ⟶ T) [IsMonHom b]
    (c : R ⟶ T) [IsMonHom c] (h : a ≫ b = c) (M : Mod C R) :
    (Mod.extendRestrictAdjunction a).unit.app M ≫
      (Mod.comap a).map ((Mod.extendRestrictAdjunction b).unit.app
        ((Mod.extendScalars a).obj M)) ≫
      ((Mod.comapComp a b).symm ≪≫ Mod.comapCongr h).hom.app
        ((Mod.extendScalars b).obj ((Mod.extendScalars a).obj M)) ≫
      (Mod.comap c).map (((Mod.extendScalarsComp a b).symm ≪≫
        (Mod.extendRestrictAdjunction _).leftAdjointUniq
          ((Mod.extendRestrictAdjunction c).ofNatIsoRight (Mod.comapCongr h).symm)).hom.app M) =
      (Mod.extendRestrictAdjunction c).unit.app M := by
  let A := ((Mod.extendRestrictAdjunction a).comp
    (Mod.extendRestrictAdjunction b)).ofNatIsoRight (Mod.comapComp a b).symm
  have h := uniqueness_transport_unit A (Mod.extendRestrictAdjunction (a ≫ b))
    (Mod.extendRestrictAdjunction c) (Mod.comapCongr h) M
  simpa only [A, Mod.extendScalarsComp, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.map_comp, Category.assoc] using h

omit [IsCommMonObj Λ₂] in
private theorem ordinary_unit (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u}) (M : Modules Λ₀ T) :
    (ordinaryAdj a T).unit.app M ≫
      (V₀ a T).map ((ordinaryAdj b T).unit.app ((extension a T).obj M)) ≫
      (resOrd a b T).hom.app ((extension b T).obj ((extension a T).obj M)) ≫
      (V₀ (a ≫ b) T).map ((ordinaryComp a b (a ≫ b) rfl T).hom.app M) =
      (ordinaryAdj (a ≫ b) T).unit.app M := by
  simpa only [ordinaryAdj, rawAdj, ordinaryComp, resOrd] using
    module_composition_unit (coefficientMap a T) (coefficientMap b T)
      (coefficientMap (a ≫ b) T) (coefficientMap_comp a b T).symm M

private theorem ordinary_pull_conjugate (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    conjugateIsoEquiv
      ((CondensedRing.upperStarLowerStarAdjunction Λ₀ f).comp (ordinaryAdj a X))
      ((ordinaryAdj a Y).comp (CondensedRing.upperStarLowerStarAdjunction Λ₁ f))
      (CondensedRing.pullIso a f).symm = (CondensedRing.comapLowerStarIso a f).symm := by
  unfold ordinaryAdj rawAdj CondensedRing.pullIso Adjunction.pullIsoOfComapIso
  rw [conjugateIsoEquiv_iso_symm]
  exact congrArg Iso.symm ((conjugateIsoEquiv _ _).apply_symm_apply _)

private theorem comap_square_inv_hom
    {C : Type u₀} [Category.{v₀} C] [MonoidalCategory C]
    {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E]
    (G : C ⥤ E) [G.LaxMonoidal]
    {R S : C} [MonObj R] [MonObj S] {R' S' : E} [MonObj R'] [MonObj S']
    (a : R ⟶ S) [IsMonHom a] (b : R' ⟶ S') [IsMonHom b]
    (r : R' ⟶ G.obj R) [IsMonHom r] (s : S' ⟶ G.obj S) [IsMonHom s]
    (h : b ≫ s = r ≫ G.map a) (M : Mod C S) :
    ((Mod.comapMapModComapIso G a b r s h).inv.app M).hom = 𝟙 (G.obj M.X) := by
  have hi := congrArg Mod.Hom.hom
    ((Mod.comapMapModComapIso G a b r s h).inv_hom_id_app M)
  change ((Mod.comapMapModComapIso G a b r s h).inv.app M).hom ≫
    ((Mod.comapMapModComapIso G a b r s h).hom.app M).hom = 𝟙 (G.obj M.X) at hi
  rw [Mod.comapMapModComapIso_hom_app_hom] at hi
  dsimp only [Functor.comp_obj, Functor.mapMod, Mod.comap] at hi
  simpa only [Category.comp_id] using hi

private theorem module_restriction_rectangle
    {C : Type u₀} [Category.{v₀} C] [MonoidalCategory C]
    {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E]
    (G : C ⥤ E) [G.LaxMonoidal]
    {R₀ R₁ R₂ : C} [MonObj R₀] [MonObj R₁] [MonObj R₂]
    {S₀ S₁ S₂ : E} [MonObj S₀] [MonObj S₁] [MonObj S₂]
    (a : R₀ ⟶ R₁) [IsMonHom a] (b : R₁ ⟶ R₂) [IsMonHom b]
    (c : R₀ ⟶ R₂) [IsMonHom c] (hc : a ≫ b = c)
    (a' : S₀ ⟶ S₁) [IsMonHom a'] (b' : S₁ ⟶ S₂) [IsMonHom b']
    (c' : S₀ ⟶ S₂) [IsMonHom c'] (hc' : a' ≫ b' = c')
    (r₀ : S₀ ⟶ G.obj R₀) [IsMonHom r₀]
    (r₁ : S₁ ⟶ G.obj R₁) [IsMonHom r₁]
    (r₂ : S₂ ⟶ G.obj R₂) [IsMonHom r₂]
    (ha : a' ≫ r₁ = r₀ ≫ G.map a) (hb : b' ≫ r₂ = r₁ ≫ G.map b)
    (hcc : c' ≫ r₂ = r₀ ≫ G.map c) :
    let f₀ := G.mapMod R₀ ⋙ Mod.comap r₀
    let f₁ := G.mapMod R₁ ⋙ Mod.comap r₁
    let f₂ := G.mapMod R₂ ⋙ Mod.comap r₂
    let e₁ := Mod.comapMapModComapIso G a a' r₀ r₁ ha
    let e₂ := Mod.comapMapModComapIso G b b' r₁ r₂ hb
    let e₃ := Mod.comapMapModComapIso G c c' r₀ r₂ hcc
    let δX := (Mod.comapComp a b).symm ≪≫ Mod.comapCongr hc
    let δY := (Mod.comapComp a' b').symm ≪≫ Mod.comapCongr hc'
    (Functor.associator (Mod.comap b) (Mod.comap a) f₀).hom ≫
      whiskerLeft (Mod.comap b) e₁.inv ≫
      (Functor.associator (Mod.comap b) f₁ (Mod.comap a')).inv ≫
      whiskerRight e₂.inv (Mod.comap a') ≫
      (Functor.associator f₂ (Mod.comap b') (Mod.comap a')).hom =
      whiskerRight δX.hom f₀ ≫ e₃.inv ≫ whiskerLeft f₂ δY.inv := by
  dsimp only
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  simp only [associator_hom_app, associator_inv_app, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Mod.comp_hom', comap_square_inv_hom, Mod.comap_map_hom,
    Mod.comapComp_inv_app_hom, Mod.comapComp_hom_app_hom,
    Mod.comapCongr, NatIso.ofComponents_inv_app,
    Mod.isoMk_inv_hom, Iso.refl_inv, Functor.comp_map,
    mapMod_map, Mod.id_hom']
  dsimp only [Functor.mapMod, Mod.comap]
  simp

private theorem ordinary_paste (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.associator (extension a Y) (extension b Y) (CondensedRing.upperStar Λ₂ f)) ≪≫
      Functor.isoWhiskerLeft (extension a Y) (CondensedRing.pullIso b f).symm ≪≫
      (Functor.associator (extension a Y) (CondensedRing.upperStar Λ₁ f)
        (extension b X)).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.pullIso a f).symm (extension b X) ≪≫
      (Functor.associator (CondensedRing.upperStar Λ₀ f) (extension a X) (extension b X)) ≪≫
      Functor.isoWhiskerLeft (CondensedRing.upperStar Λ₀ f)
        (ordinaryComp a b (a ≫ b) rfl X) =
      Functor.isoWhiskerRight (ordinaryComp a b (a ≫ b) rfl Y)
        (CondensedRing.upperStar Λ₂ f) ≪≫ (CondensedRing.pullIso (a ≫ b) f).symm := by
  apply rectangle (ordinaryAdj a Y) (ordinaryAdj b Y) (ordinaryAdj (a ≫ b) Y)
    (ordinaryAdj a X) (ordinaryAdj b X) (ordinaryAdj (a ≫ b) X)
    (CondensedRing.upperStarLowerStarAdjunction Λ₀ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ₁ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ₂ f)
    _ _ _ _ _ (resOrd a b Y) (resOrd a b X)
    (CondensedRing.comapLowerStarIso a f) (CondensedRing.comapLowerStarIso b f)
    (CondensedRing.comapLowerStarIso (a ≫ b) f)
  · apply conjugate_of_unit
    intro M
    simpa only [Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc] using
      ordinary_unit a b Y M
  · apply conjugate_of_unit
    intro M
    simpa only [Adjunction.comp_unit_app, Functor.comp_obj, Category.assoc] using
      ordinary_unit a b X M
  · exact ordinary_pull_conjugate a f
  · exact ordinary_pull_conjugate b f
  · exact ordinary_pull_conjugate (a ≫ b) f
  · exact module_restriction_rectangle _
      (coefficientMap a X) (coefficientMap b X) (coefficientMap (a ≫ b) X)
      (coefficientMap_comp a b X).symm
      (coefficientMap a Y) (coefficientMap b Y) (coefficientMap (a ≫ b) Y)
      (coefficientMap_comp a b Y).symm
      (condensedPushforwardHom Λ₀ f) (condensedPushforwardHom Λ₁ f)
      (condensedPushforwardHom Λ₂ f)
      (condensedPushforwardHom_comp_map_coefficientMap a f).symm
      (condensedPushforwardHom_comp_map_coefficientMap b f).symm
      (condensedPushforwardHom_comp_map_coefficientMap (a ≫ b) f).symm

private def resOrdEq (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (c : Λ₀ ⟶ Λ₂) [IsMonHom c]
    (h : a ≫ b = c) (T : Scheme.{u}) : V₀ b T ⋙ V₀ a T ≅ V₀ c T :=
  (Mod.comapComp (coefficientMap a T) (coefficientMap b T)).symm ≪≫
    Mod.comapCongr ((coefficientMap_comp a b T).symm.trans
      (congrArg (fun d ↦ coefficientMap d T) h))

omit [IsCommMonObj Λ₂] in
private theorem ordinary_unit_eq (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (c : Λ₀ ⟶ Λ₂) [IsMonHom c]
    (h : a ≫ b = c) (T : Scheme.{u}) (M : Modules Λ₀ T) :
    (ordinaryAdj a T).unit.app M ≫
      (V₀ a T).map ((ordinaryAdj b T).unit.app ((extension a T).obj M)) ≫
      (resOrdEq a b c h T).hom.app ((extension b T).obj ((extension a T).obj M)) ≫
      (V₀ c T).map ((ordinaryComp a b c h T).hom.app M) =
      (ordinaryAdj c T).unit.app M := by
  subst c
  exact ordinary_unit a b T M

private theorem identity_square
    {A B : Type*} [Category A] [Category B]
    {EY RY : A ⥤ A} {EX RX : B ⥤ B} {U : A ⥤ B} {F : B ⥤ A}
    (AY : EY ⊣ RY) (AX : EX ⊣ RX) (AF : U ⊣ F)
    (eY : EY ≅ 𝟭 A) (eX : EX ≅ 𝟭 B) (rY : RY ≅ 𝟭 A) (rX : RX ≅ 𝟭 B)
    (θ : EY ⋙ U ≅ U ⋙ EX) (r : F ⋙ RY ≅ RX ⋙ F)
    (hY : conjugateIsoEquiv Adjunction.id AY eY = rY.symm)
    (hX : conjugateIsoEquiv Adjunction.id AX eX = rX.symm)
    (hθ : conjugateIsoEquiv (AF.comp AX) (AY.comp AF) θ = r.symm)
    (hr : r = isoWhiskerLeft F rY ≪≫ F.rightUnitor ≪≫
      F.leftUnitor.symm ≪≫ isoWhiskerRight rX.symm F) :
    θ = isoWhiskerRight eY U ≪≫ U.leftUnitor ≪≫ U.rightUnitor.symm ≪≫
      isoWhiskerLeft U eX.symm := by
  apply (conjugateIsoEquiv (AF.comp AX) (AY.comp AF)).injective
  conv_rhs => rw [← Iso.trans_assoc, ← Iso.trans_assoc]
  rw [conjugateIsoEquiv_trans _ (AF.comp Adjunction.id),
    conjugateIsoEquiv_trans _ AF,
    conjugateIsoEquiv_trans _ (Adjunction.id.comp AF)]
  rw [conjugateIsoEquiv_isoWhiskerLeft AX Adjunction.id AF,
    conjugateIsoEquiv_iso_symm, hX,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_rightUnitor,
    conjugateIsoEquiv_leftUnitor,
    conjugateIsoEquiv_isoWhiskerRight Adjunction.id AY AF, hY, hθ, hr]
  simp only [Iso.trans_symm, Iso.trans_assoc]
  rfl

omit [IsCommMonObj Λ₁] in
private def scalarComp (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u}) :
    D a T ⋙ D b T ≅ D (a ≫ b) T :=
  (((scalarAdj a T).comp (scalarAdj b T)).ofNatIsoRight
    (scalarRestrictionComp a b T)).leftAdjointUniq (scalarAdj (a ≫ b) T)

attribute [local irreducible] scalarComp

private theorem composed_unique_unit
    {C E H : Type*} [Category* C] [Category* E] [Category* H]
    {A : C ⥤ E} {B : E ⥤ H} {AB : C ⥤ H}
    {R : E ⥤ C} {S : H ⥤ E} {RS : H ⥤ C}
    (a : A ⊣ R) (b : B ⊣ S) (ab : AB ⊣ RS) (δ : S ⋙ R ≅ RS) (K : C) :
    a.unit.app K ≫ R.map (b.unit.app (A.obj K)) ≫
      R.map (S.map ((((a.comp b).ofNatIsoRight δ).leftAdjointUniq ab).hom.app K)) ≫
      δ.hom.app (AB.obj K) = ab.unit.app K := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((a.comp b).ofNatIsoRight δ) ab K
  simpa only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj, Functor.comp_map,
    Category.assoc, ← δ.hom.naturality] using h

private theorem composed_unique_transpose
    {C E H : Type*} [Category* C] [Category* E] [Category* H]
    {A : C ⥤ E} {B : E ⥤ H} {AB : C ⥤ H}
    {R : E ⥤ C} {S : H ⥤ E} {RS : H ⥤ C}
    (a : A ⊣ R) (b : B ⊣ S) (ab : AB ⊣ RS) (δ : S ⋙ R ≅ RS)
    (K : C) (N : H) (g : K ⟶ RS.obj N) :
    (a.comp b).homEquiv K N
      ((((a.comp b).ofNatIsoRight δ).leftAdjointUniq ab).hom.app K ≫
        (ab.homEquiv K N).symm g) = g ≫ δ.inv.app N := by
  apply (cancel_mono (δ.hom.app N)).1
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [Adjunction.unit_leftAdjointUniq_hom_app]
  exact (ab.homEquiv K N).apply_symm_apply g

private theorem scalarComp_unit (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u})
    (K : DerivedCategory (Modules Λ₀ T)) :
    (scalarAdj a T).unit.app K ≫
      (V a T).map ((scalarAdj b T).unit.app ((D a T).obj K)) ≫
      (V a T).map ((V b T).map ((scalarComp a b T).hom.app K)) ≫
      (scalarRestrictionComp a b T).hom.app ((D (a ≫ b) T).obj K) =
    (scalarAdj (a ≫ b) T).unit.app K := by
  unfold scalarComp
  exact composed_unique_unit (scalarAdj a T) (scalarAdj b T) (scalarAdj (a ≫ b) T)
    (scalarRestrictionComp a b T) K

private theorem scalarComp_transpose (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u})
    (K : DerivedCategory (Modules Λ₀ T)) (H : DerivedCategory (Modules Λ₂ T))
    (g : K ⟶ (V (a ≫ b) T).obj H) :
    ((scalarAdj a T).comp (scalarAdj b T)).homEquiv K H
      ((scalarComp a b T).hom.app K ≫
        ((scalarAdj (a ≫ b) T).homEquiv K H).symm g) =
      g ≫ (scalarRestrictionComp a b T).inv.app H := by
  unfold scalarComp
  exact composed_unique_transpose (scalarAdj a T) (scalarAdj b T)
    (scalarAdj (a ≫ b) T) (scalarRestrictionComp a b T) K H g

section ExactComposition

private local instance exact_comp_limits {A B E : Type*}
    [Category A] [Category B] [Category E] (F : A ⥤ B) (G : B ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G

private local instance exact_comp_colimits {A B E : Type*}
    [Category A] [Category B] [Category E] (F : A ⥤ B) (G : B ⥤ E)
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] :
    PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G

private theorem exact_comp_normalization
    {A : Type u₀} {B : Type u₁} {C : Type u₂}
    [Category.{v₀} A] [Category.{v₁} B] [Category.{v₂} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w₁} B]
    [HasDerivedCategory.{w₂} C]
    (R : B ⥤ A) (S : C ⥤ B) (U : C ⥤ A)
    [R.Additive] [S.Additive] [U.Additive]
    [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteLimits S]
    [Limits.PreservesFiniteLimits U]
    [Limits.PreservesFiniteColimits R] [Limits.PreservesFiniteColimits S]
    [Limits.PreservesFiniteColimits U] (e : S ⋙ R ≅ U)
    (H : HomotopyCategory C (.up ℤ)) :
    (mapDerivedCategoryCompIso S R ≪≫ mapDerivedCategoryNatIso e).hom.app
        (DerivedCategory.Qh.obj H) ≫ U.mapDerivedCategoryFactorsh.hom.app H =
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactorsh.hom.app H) ≫
        R.mapDerivedCategoryFactorsh.hom.app ((S.mapHomotopyCategory (.up ℤ)).obj H) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso e (.up ℤ)).hom.app H) := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, mapDerivedCategoryNatIso_fach]
  rw [← mapDerivedCategoryCompIso_fach S R]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← DerivedCategory.Qh.map_comp]
  congr 2
  congr 1
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  change (HomotopyCategory.quotient A (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient A (.up ℤ)).map _ =
    (HomotopyCategory.quotient A (.up ℤ)).map _
  rw [← Functor.map_comp]
  congr 1
  ext n : 1
  exact Category.id_comp _

end ExactComposition

private theorem homotopy_unit
    {A : Type u₀} {B : Type u₁} {C : Type u₂}
    [Category.{v₀} A] [Category.{v₁} B] [Category.{v₂} C]
    [Abelian A] [Abelian B] [Abelian C]
    (E : A ⥤ B) (F : B ⥤ C) (G : A ⥤ C)
    (R : B ⥤ A) (S : C ⥤ B) (U : C ⥤ A)
    [E.Additive] [F.Additive] [G.Additive]
    [R.Additive] [S.Additive] [U.Additive]
    (a : E ⊣ R) (b : F ⊣ S) (c : G ⊣ U)
    (r : S ⋙ R ≅ U) (e : E ⋙ F ≅ G)
    (hu : ∀ M, a.unit.app M ≫ R.map (b.unit.app (E.obj M)) ≫
      r.hom.app (F.obj (E.obj M)) ≫ U.map (e.hom.app M) = c.unit.app M)
    (H : HomotopyCategory A (.up ℤ)) :
    (a.mapHomotopyCategory (.up ℤ)).unit.app H ≫
      (R.mapHomotopyCategory (.up ℤ)).map
        ((b.mapHomotopyCategory (.up ℤ)).unit.app
          ((E.mapHomotopyCategory (.up ℤ)).obj H)) ≫
      (mapHomotopyCategoryCompIso r (.up ℤ)).hom.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((E.mapHomotopyCategory (.up ℤ)).obj H)) ≫
      (U.mapHomotopyCategory (.up ℤ)).map
        ((mapHomotopyCategoryCompIso e (.up ℤ)).hom.app H) =
      (c.mapHomotopyCategory (.up ℤ)).unit.app H := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  have hb := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ) b
    ((E.mapHomologicalComplex (.up ℤ)).obj P)
  simp only [Adjunction.mapHomotopyCategory_unit_app_quotient]
  erw [hb]
  change (HomotopyCategory.quotient A (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient A (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient A (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient A (.up ℤ)).map _ =
    (HomotopyCategory.quotient A (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  exact hu (P.X n)

omit [IsCommMonObj Λ₀] [IsCommMonObj Λ₁] [IsCommMonObj Λ₂] in
private theorem resComp_normalization (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u})
    (H : HomotopyCategory (Modules Λ₂ T) (.up ℤ)) :
    (scalarRestrictionComp a b T).hom.app (DerivedCategory.Qh.obj H) ≫
      (V₀ (a ≫ b) T).mapDerivedCategoryFactorsh.hom.app H =
    (V a T).map ((V₀ b T).mapDerivedCategoryFactorsh.hom.app H) ≫
      (V₀ a T).mapDerivedCategoryFactorsh.hom.app
        (((V₀ b T).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (resOrd a b T) (.up ℤ)).hom.app H) := by
  unfold scalarRestrictionComp
  exact exact_comp_normalization (V₀ a T) (V₀ b T) (V₀ (a ≫ b) T)
    (resOrd a b T) H

omit [IsCommMonObj Λ₀] [IsCommMonObj Λ₁] [IsCommMonObj Λ₂] in
private theorem resComp_inverse_normalization (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u})
    (H : HomotopyCategory (Modules Λ₂ T) (.up ℤ)) :
    (V₀ a T).mapDerivedCategoryFactorsh.inv.app
        (((V₀ b T).mapHomotopyCategory (.up ℤ)).obj H) ≫
      (V a T).map ((V₀ b T).mapDerivedCategoryFactorsh.inv.app H) ≫
      (scalarRestrictionComp a b T).hom.app (DerivedCategory.Qh.obj H) =
    DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (resOrd a b T) (.up ℤ)).hom.app H) ≫
      (V₀ (a ≫ b) T).mapDerivedCategoryFactorsh.inv.app H := by
  apply (cancel_mono ((V₀ (a ≫ b) T).mapDerivedCategoryFactorsh.hom.app H)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [resComp_normalization]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(V a T).map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact (Category.comp_id _).symm

omit [IsCommMonObj Λ₂] in
private theorem ordinary_homotopy_unit (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u})
    (H : HomotopyCategory (Modules Λ₀ T) (.up ℤ)) :
    ((ordinaryAdj a T).mapHomotopyCategory (.up ℤ)).unit.app H ≫
      ((V₀ a T).mapHomotopyCategory (.up ℤ)).map
        (((ordinaryAdj b T).mapHomotopyCategory (.up ℤ)).unit.app
          (((extension a T).mapHomotopyCategory (.up ℤ)).obj H)) ≫
      (Functor.mapHomotopyCategoryCompIso (resOrd a b T) (.up ℤ)).hom.app
        (((extension b T).mapHomotopyCategory (.up ℤ)).obj
          (((extension a T).mapHomotopyCategory (.up ℤ)).obj H)) ≫
      ((V₀ (a ≫ b) T).mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso
          (ordinaryComp a b (a ≫ b) rfl T) (.up ℤ)).hom.app H) =
      ((ordinaryAdj (a ≫ b) T).mapHomotopyCategory (.up ℤ)).unit.app H := by
  exact homotopy_unit (extension a T) (extension b T) (extension (a ≫ b) T)
    (V₀ a T) (V₀ b T) (V₀ (a ≫ b) T) (ordinaryAdj a T) (ordinaryAdj b T)
    (ordinaryAdj (a ≫ b) T) (resOrd a b T) (ordinaryComp a b (a ≫ b) rfl T)
    (ordinary_unit a b T) H

private theorem homotopy_comp_refl_inv
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (P : HomotopyCategory A (.up ℤ)) :
    (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app P = 𝟙 _ := by
  have h := Iso.inv_hom_id_app
    (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) P
  rw [mapHomotopyCategoryCompIso_refl_hom_app] at h
  simpa only [Category.comp_id] using h

private theorem scalar_post_ext (a : Λ₀ ⟶ Λ₁) [IsMonHom a] (T : Scheme.{u})
    {C : Type*} [Category* C] (H : DerivedCategory (Modules Λ₁ T) ⥤ C)
    {G : DerivedCategory (Modules Λ₀ T) ⥤ C} (α β : G ⟶ D a T ⋙ H)
    (h : ∀ P : HomotopyCategory (Modules Λ₀ T) (.up ℤ),
      α.app (DerivedCategory.Qh.obj P) ≫ H.map ((scalarCounit a T).app P) =
        β.app (DerivedCategory.Qh.obj P) ≫ H.map ((scalarCounit a T).app P)) : α = β := by
  unfold D at α β ⊢
  unfold scalarCounit D at h
  exact derived_post_ext (extension a T) H α β h

private theorem pullCounit_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (pullCounit (Λ := Λ) f) := by
  unfold pullCounit L CondensedRing.moduleObjectDerivedPullback
  exact Functor.isIso_leftDerivedFunctorCounit (CondensedRing.upperStar Λ f)

private theorem normalized_pull_ext (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : D a Y ⋙ L Λ₁ f ≅ L Λ₀ f ⋙ D a X) (hl : PullNormalized a f l)
    {G : DerivedCategory (Modules Λ₀ Y) ⥤ DerivedCategory (Modules Λ₁ X)}
    (α β : G ⟶ L Λ₀ f ⋙ D a X)
    (h : ∀ P : HomotopyCategory (Modules Λ₀ Y) (.up ℤ),
      α.app (DerivedCategory.Qh.obj P) ≫ (D a X).map ((pullCounit (Λ := Λ₀) f).app P) ≫
        (scalarCounit a X).app
          (((CondensedRing.upperStar Λ₀ f).mapHomotopyCategory (.up ℤ)).obj P) =
      β.app (DerivedCategory.Qh.obj P) ≫ (D a X).map ((pullCounit (Λ := Λ₀) f).app P) ≫
        (scalarCounit a X).app
          (((CondensedRing.upperStar Λ₀ f).mapHomotopyCategory (.up ℤ)).obj P)) : α = β := by
  apply (cancel_mono l.inv).1
  apply scalar_post_ext a Y (L Λ₁ f)
  intro P
  have : IsIso (pullCounit (Λ := Λ₁) f) := pullCounit_isIso Λ₁ f
  apply (cancel_mono ((pullCounit (Λ := Λ₁) f).app
    (((extension a Y).mapHomotopyCategory (.up ℤ)).obj P))).1
  apply (cancel_mono (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
    (CondensedRing.pullIso a f).symm (.up ℤ)).hom.app P))).1
  have hn := hl P
  simp only [NatTrans.comp_app, Category.assoc]
  rw [← hn]
  simp only [Iso.inv_hom_id_app_assoc]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (CondensedRing.upperStar Λ₀ f ⋙ extension a X)) (.up ℤ)).hom.app P)) (h P)

section NormalizedComposition
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  {DA : Type u₄} {DB : Type u₅} {DC : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Category.{v₄} DA] [Category.{v₅} DB] [Category.{v₆} DC]
  {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
  {FD : DA ⥤ DB} {RD : DB ⥤ DA} {GD : DB ⥤ DC} {SD : DC ⥤ DB}
  {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}

private theorem normalized_composition
    {H : A ⥤ C} {U : C ⥤ A} {HD : DA ⥤ DC} {UD : DC ⥤ DA}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ U)
    (ad : FD ⊣ RD) (bd : GD ⊣ SD) (cd : HD ⊣ UD)
    (εF : QA ⋙ FD ⟶ F ⋙ QB) (εG : QB ⋙ GD ⟶ G ⋙ QC)
    (εH : QA ⋙ HD ⟶ H ⋙ QC)
    (ρF : R ⋙ QA ⟶ QB ⋙ RD) (ρG : S ⋙ QB ⟶ QC ⋙ SD)
    (ρH : U ⋙ QA ⟶ QC ⋙ UD)
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF.app K)
    (hG : ∀ P K (f : G.obj P ⟶ K),
      bd.homEquiv _ _ (εG.app P ≫ QC.map f) = QB.map (b.homEquiv _ _ f) ≫ ρG.app K)
    (hH : ∀ P K (f : H.obj P ⟶ K),
      cd.homEquiv _ _ (εH.app P ≫ QC.map f) = QA.map (c.homEquiv _ _ f) ≫ ρH.app K)
    (η : S ⋙ R ≅ U) (δ : SD ⋙ RD ≅ UD) (ν : F ⋙ G ≅ H)
    (hu : ∀ P, a.unit.app P ≫ R.map (b.unit.app (F.obj P)) ≫
      η.hom.app (G.obj (F.obj P)) ≫ U.map (ν.hom.app P) = c.unit.app P)
    (hr : ∀ K, ρF.app (S.obj K) ≫ RD.map (ρG.app K) ≫ δ.hom.app (QC.obj K) =
      QA.map (η.hom.app K) ≫ ρH.app K)
    (P : A) :
    (((ad.comp bd).ofNatIsoRight δ).leftAdjointUniq cd).hom.app (QA.obj P) ≫
      εH.app P = GD.map (εF.app P) ≫ εG.app (F.obj P) ≫ QC.map (ν.hom.app P) := by
  symm
  rw [← Category.assoc]
  symm
  apply normalizedAdjunction_uniqueness (a.comp b) c (ad.comp bd) cd
    (fun P ↦ GD.map (εF.app P) ≫ εG.app (F.obj P)) (fun P ↦ εH.app P)
    (fun K ↦ ρF.app (S.obj K) ≫ RD.map (ρG.app K)) (fun K ↦ ρH.app K)
    (fun P K f ↦ ?_) hH η δ (fun P ↦ ν.hom.app P) (fun P ↦ ?_)
    (fun K ↦ (Category.assoc _ _ _).trans (hr K)) P
  · simpa only [Category.assoc] using
      normalizedAdjunction_composition a b ad bd εF εG ρF ρG hF hG P K f
  · rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
    simp only [Functor.comp_map, Category.assoc]
    have hn := η.hom.naturality (ν.hom.app P)
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    exact hu P

end NormalizedComposition

private theorem scalarComp_normalized (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] (T : Scheme.{u}) :
    SuccessiveNormalized a b (a ≫ b) rfl T (scalarComp a b T) := by
  intro P
  unfold scalarComp
  exact normalized_composition
    ((ordinaryAdj a T).mapHomotopyCategory (.up ℤ))
    ((ordinaryAdj b T).mapHomotopyCategory (.up ℤ))
    ((ordinaryAdj (a ≫ b) T).mapHomotopyCategory (.up ℤ))
    (scalarAdj a T) (scalarAdj b T) (scalarAdj (a ≫ b) T)
    (scalarCounit a T) (scalarCounit b T) (scalarCounit (a ≫ b) T)
    (V₀ a T).mapDerivedCategoryFactorsh.inv
    (V₀ b T).mapDerivedCategoryFactorsh.inv
    (V₀ (a ≫ b) T).mapDerivedCategoryFactorsh.inv
    (scalar_hom_comparison a T) (scalar_hom_comparison b T)
    (scalar_hom_comparison (a ≫ b) T)
    (Functor.mapHomotopyCategoryCompIso (resOrd a b T) (.up ℤ))
    (scalarRestrictionComp a b T)
    (Functor.mapHomotopyCategoryCompIso (ordinaryComp a b (a ≫ b) rfl T) (.up ℤ))
    (ordinary_homotopy_unit a b T) (resComp_inverse_normalization a b T) P

attribute [local irreducible] resOrd CondensedRing.pullIso

private theorem homotopy_paste
    {A₀ : Type*} [Category A₀] [Preadditive A₀]
    {A₁ : Type*} [Category A₁] [Preadditive A₁]
    {A₂ : Type*} [Category A₂] [Preadditive A₂]
    {B₀ : Type*} [Category B₀] [Preadditive B₀]
    {B₁ : Type*} [Category B₁] [Preadditive B₁]
    {B₂ : Type*} [Category B₂] [Preadditive B₂]
    {E : A₀ ⥤ A₁} [E.Additive]
    {G : A₁ ⥤ A₂} [G.Additive]
    {H : A₀ ⥤ A₂} [H.Additive]
    {e : B₀ ⥤ B₁} [e.Additive]
    {g : B₁ ⥤ B₂} [g.Additive]
    {h : B₀ ⥤ B₂} [h.Additive]
    {U₀ : A₀ ⥤ B₀} [U₀.Additive]
    {U₁ : A₁ ⥤ B₁} [U₁.Additive]
    {U₂ : A₂ ⥤ B₂} [U₂.Additive]
    (σA : E ⋙ G ≅ H) (σB : e ⋙ g ≅ h)
    (θE : E ⋙ U₁ ≅ U₀ ⋙ e) (θG : G ⋙ U₂ ≅ U₁ ⋙ g)
    (θH : H ⋙ U₂ ≅ U₀ ⋙ h)
    (hp : ∀ M, θG.hom.app (E.obj M) ≫ g.map (θE.hom.app M) ≫
      σB.hom.app (U₀.obj M) = U₂.map (σA.hom.app M) ≫ θH.hom.app M)
    (P : HomotopyCategory A₀ (.up ℤ)) :
    (mapHomotopyCategoryCompIso θG (.up ℤ)).hom.app
        ((E.mapHomotopyCategory (.up ℤ)).obj P) ≫
      (g.mapHomotopyCategory (.up ℤ)).map
        ((mapHomotopyCategoryCompIso θE (.up ℤ)).hom.app P) ≫
      (mapHomotopyCategoryCompIso σB (.up ℤ)).hom.app
        ((U₀.mapHomotopyCategory (.up ℤ)).obj P) =
      (U₂.mapHomotopyCategory (.up ℤ)).map
        ((mapHomotopyCategoryCompIso σA (.up ℤ)).hom.app P) ≫
      (mapHomotopyCategoryCompIso θH (.up ℤ)).hom.app P := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient B₂ (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient B₂ (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient B₂ (.up ℤ)).map _ =
    (HomotopyCategory.quotient B₂ (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient B₂ (.up ℤ)).map _
  simp only [← Functor.map_comp]
  congr 1
  ext n : 1
  exact hp (P.X n)

private theorem paste_normalization
    {A₀ : Type*} [Category A₀]
    {A₁ : Type*} [Category A₁]
    {A₂ : Type*} [Category A₂]
    {B₀ : Type*} [Category B₀]
    {B₁ : Type*} [Category B₁]
    {B₂ : Type*} [Category B₂]
    {DA₀ : Type*} [Category DA₀]
    {DA₁ : Type*} [Category DA₁]
    {DA₂ : Type*} [Category DA₂]
    {DB₀ : Type*} [Category DB₀]
    {DB₁ : Type*} [Category DB₁]
    {DB₂ : Type*} [Category DB₂]
    {E : A₀ ⥤ A₁} {ED : DA₀ ⥤ DA₁}
    {G : A₁ ⥤ A₂} {GD : DA₁ ⥤ DA₂}
    {H : A₀ ⥤ A₂} {HD : DA₀ ⥤ DA₂}
    {e : B₀ ⥤ B₁} {eD : DB₀ ⥤ DB₁}
    {g : B₁ ⥤ B₂} {gD : DB₁ ⥤ DB₂}
    {h : B₀ ⥤ B₂} {hD : DB₀ ⥤ DB₂}
    {U₀ : A₀ ⥤ B₀} {U₀D : DA₀ ⥤ DB₀}
    {U₁ : A₁ ⥤ B₁} {U₁D : DA₁ ⥤ DB₁}
    {U₂ : A₂ ⥤ B₂} {U₂D : DA₂ ⥤ DB₂}
    {QA₀ : A₀ ⥤ DA₀} {QB₀ : B₀ ⥤ DB₀}
    {QA₁ : A₁ ⥤ DA₁} {QB₁ : B₁ ⥤ DB₁}
    {QA₂ : A₂ ⥤ DA₂} {QB₂ : B₂ ⥤ DB₂}
    (εE : QA₀ ⋙ ED ⟶ E ⋙ QA₁)
    (εG : QA₁ ⋙ GD ⟶ G ⋙ QA₂)
    (εH : QA₀ ⋙ HD ⟶ H ⋙ QA₂)
    (εe : QB₀ ⋙ eD ⟶ e ⋙ QB₁)
    (εg : QB₁ ⋙ gD ⟶ g ⋙ QB₂)
    (εh : QB₀ ⋙ hD ⟶ h ⋙ QB₂)
    (εU₀ : QA₀ ⋙ U₀D ⟶ U₀ ⋙ QB₀)
    (εU₁ : QA₁ ⋙ U₁D ⟶ U₁ ⋙ QB₁)
    (εU₂ : QA₂ ⋙ U₂D ⟶ U₂ ⋙ QB₂)
    (σA : E ⋙ G ⟶ H) (σB : e ⋙ g ⟶ h)
    (θE : E ⋙ U₁ ⟶ U₀ ⋙ e) (θG : G ⋙ U₂ ⟶ U₁ ⋙ g)
    (θH : H ⋙ U₂ ⟶ U₀ ⋙ h)
    (βA : ED ⋙ GD ⟶ HD) (βB : eD ⋙ gD ⟶ hD)
    (lE : ED ⋙ U₁D ⟶ U₀D ⋙ eD) (lG : GD ⋙ U₂D ⟶ U₁D ⋙ gD)
    (lH : HD ⋙ U₂D ⟶ U₀D ⋙ hD)
    (hβA : ∀ P, βA.app (QA₀.obj P) ≫ εH.app P =
      GD.map (εE.app P) ≫ εG.app (E.obj P) ≫ QA₂.map (σA.app P))
    (hβB : ∀ P, βB.app (QB₀.obj P) ≫ εh.app P =
      gD.map (εe.app P) ≫ εg.app (e.obj P) ≫ QB₂.map (σB.app P))
    (hlE : ∀ P, lE.app (QA₀.obj P) ≫ eD.map (εU₀.app P) ≫ εe.app (U₀.obj P) =
      U₁D.map (εE.app P) ≫ εU₁.app (E.obj P) ≫ QB₁.map (θE.app P))
    (hlG : ∀ P, lG.app (QA₁.obj P) ≫ gD.map (εU₁.app P) ≫ εg.app (U₁.obj P) =
      U₂D.map (εG.app P) ≫ εU₂.app (G.obj P) ≫ QB₂.map (θG.app P))
    (hlH : ∀ P, lH.app (QA₀.obj P) ≫ hD.map (εU₀.app P) ≫ εh.app (U₀.obj P) =
      U₂D.map (εH.app P) ≫ εU₂.app (H.obj P) ≫ QB₂.map (θH.app P))
    (hp : ∀ P, θG.app (E.obj P) ≫ g.map (θE.app P) ≫ σB.app (U₀.obj P) =
      U₂.map (σA.app P) ≫ θH.app P)
    (P : A₀) :
    (lG.app (ED.obj (QA₀.obj P)) ≫ gD.map (lE.app (QA₀.obj P)) ≫
      βB.app (U₀D.obj (QA₀.obj P))) ≫ hD.map (εU₀.app P) ≫ εh.app (U₀.obj P) =
    (U₂D.map (βA.app (QA₀.obj P)) ≫ lH.app (QA₀.obj P)) ≫
      hD.map (εU₀.app P) ≫ εh.app (U₀.obj P) := by
  have nβ := βB.naturality (εU₀.app P)
  have ne := εg.naturality (θE.app P)
  have nl := lG.naturality (εE.app P)
  have nu := εU₂.naturality (σA.app P)
  dsimp only [Functor.comp_obj, Functor.comp_map] at nβ ne nl nu
  simp only [Category.assoc]
  rw [← reassoc_of% nβ, hβB]
  simp only [← Functor.map_comp_assoc]
  rw [hlE]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ne]
  rw [← reassoc_of% nl, reassoc_of% hlG (E.obj P)]
  rw [hlH]
  simp only [← Functor.map_comp_assoc]
  rw [hβA]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nu]
  rw [← QB₂.map_comp, ← QB₂.map_comp, hp]
  rw [QB₂.map_comp]

private theorem pull_normalized (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : D a Y ⋙ L Λ₁ f ≅ L Λ₀ f ⋙ D a X) (hl : PullNormalized a f l)
    (P : HomotopyCategory (Modules Λ₀ Y) (.up ℤ)) :
    l.hom.app (DerivedCategory.Qh.obj P) ≫
      (D a X).map ((pullCounit (Λ := Λ₀) f).app P) ≫
      (scalarCounit a X).app
        (((CondensedRing.upperStar Λ₀ f).mapHomotopyCategory (.up ℤ)).obj P) =
      (L Λ₁ f).map ((scalarCounit a Y).app P) ≫
        (pullCounit (Λ := Λ₁) f).app
          (((extension a Y).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (CondensedRing.pullIso a f).symm (.up ℤ)).hom.app
            P) := by
  have h := hl P
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

attribute [local irreducible] Functor.mapHomotopyCategoryCompIso
  Functor.mapHomotopyCategoryIdIso Functor.mapDerivedCategoryNatIso
  NatTrans.mapHomotopyCategory

private theorem scalar_pull_paste (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    (b : Λ₁ ⟶ Λ₂) [IsMonHom b] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l01 : D a Y ⋙ L Λ₁ f ≅ L Λ₀ f ⋙ D a X)
    (l12 : D b Y ⋙ L Λ₂ f ≅ L Λ₁ f ⋙ D b X)
    (l02 : D (a ≫ b) Y ⋙ L Λ₂ f ≅ L Λ₀ f ⋙ D (a ≫ b) X)
    (h01 : PullNormalized a f l01) (h12 : PullNormalized b f l12)
    (h02 : PullNormalized (a ≫ b) f l02)
    (K : DerivedCategory (Modules Λ₀ Y)) :
    l12.hom.app ((D a Y).obj K) ≫ (D b X).map (l01.hom.app K) ≫
      (scalarComp a b X).hom.app ((L Λ₀ f).obj K) =
      (L Λ₂ f).map ((scalarComp a b Y).hom.app K) ≫ l02.hom.app K := by
  let α : (D a Y ⋙ D b Y) ⋙ L Λ₂ f ⟶ L Λ₀ f ⋙ D (a ≫ b) X :=
    (Functor.associator _ _ _).hom ≫ whiskerLeft (D a Y) l12.hom ≫
      (Functor.associator _ _ _).inv ≫ whiskerRight l01.hom (D b X) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft (L Λ₀ f) (scalarComp a b X).hom
  let β : (D a Y ⋙ D b Y) ⋙ L Λ₂ f ⟶ L Λ₀ f ⋙ D (a ≫ b) X :=
    whiskerRight (scalarComp a b Y).hom (L Λ₂ f) ≫ l02.hom
  have hab : α = β := by
    apply normalized_pull_ext (a ≫ b) f l02 h02
    intro P
    simp only [α, β, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp]
    apply paste_normalization
      (scalarCounit a Y) (scalarCounit b Y) (scalarCounit (a ≫ b) Y)
      (scalarCounit a X) (scalarCounit b X) (scalarCounit (a ≫ b) X)
      (pullCounit (Λ := Λ₀) f) (pullCounit (Λ := Λ₁) f) (pullCounit (Λ := Λ₂) f)
      (Functor.mapHomotopyCategoryCompIso (ordinaryComp a b (a ≫ b) rfl Y) (.up ℤ)).hom
      (Functor.mapHomotopyCategoryCompIso (ordinaryComp a b (a ≫ b) rfl X) (.up ℤ)).hom
      ((Functor.mapHomotopyCategoryCompIso (CondensedRing.pullIso a f).symm (.up ℤ)).hom ≫
        (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (CondensedRing.upperStar Λ₀ f ⋙ extension a X)) (.up ℤ)).inv)
      ((Functor.mapHomotopyCategoryCompIso (CondensedRing.pullIso b f).symm (.up ℤ)).hom ≫
        (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (CondensedRing.upperStar Λ₁ f ⋙ extension b X)) (.up ℤ)).inv)
      ((Functor.mapHomotopyCategoryCompIso (CondensedRing.pullIso (a ≫ b) f).symm
          (.up ℤ)).hom ≫ (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (CondensedRing.upperStar Λ₀ f ⋙ extension (a ≫ b) X)) (.up ℤ)).inv)
      (scalarComp a b Y).hom (scalarComp a b X).hom l01.hom l12.hom l02.hom
      (scalarComp_normalized a b Y) (scalarComp_normalized a b X)
      (fun P ↦ ?_) (fun P ↦ ?_) (fun P ↦ ?_) (fun P ↦ ?_) P
    · simpa only [NatTrans.comp_app, homotopy_comp_refl_inv,
        Category.comp_id] using pull_normalized a f _ h01 P
    · simpa only [NatTrans.comp_app, homotopy_comp_refl_inv,
        Category.comp_id] using pull_normalized b f _ h12 P
    · simpa only [NatTrans.comp_app, homotopy_comp_refl_inv,
        Category.comp_id] using pull_normalized (a ≫ b) f _ h02 P
    · simp only [NatTrans.comp_app, homotopy_comp_refl_inv,
        Category.comp_id]
      apply homotopy_paste
      intro M
      have hp := NatTrans.congr_app (congrArg Iso.hom (ordinary_paste a b f)) M
      simpa only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
        isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id] using hp
  simpa only [α, β, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using NatTrans.congr_app hab K

private theorem rho_counit (a : Λ₀ ⟶ Λ₁) [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : D a Y ⋙ L Λ₁ f ≅ L Λ₀ f ⋙ D a X)
    (K : DerivedCategory (Modules Λ₀ X)) :
    (L Λ₁ f).map ((rho a f l).app K) ≫
        (adj Λ₁ f).counit.app ((D a X).obj K) =
      l.hom.app ((F Λ₀ f).obj K) ≫ (D a X).map ((adj Λ₀ f).counit.app K) :=
  mateEquiv_counit (adj Λ₀ f) (adj Λ₁ f) (TwoSquare.mk _ _ _ _ l.hom) K

attribute [local irreducible] rho

private theorem mate_rectangle
    {Y₀ Y₁ Y₂ X₀ X₁ X₂ : Type*}
    [Category Y₀] [Category Y₁] [Category Y₂]
    [Category X₀] [Category X₁] [Category X₂]
    {aY : Y₀ ⥤ Y₁} {bY : Y₁ ⥤ Y₂} {cY : Y₀ ⥤ Y₂}
    {aX : X₀ ⥤ X₁} {bX : X₁ ⥤ X₂} {cX : X₀ ⥤ X₂}
    {l₀ : Y₀ ⥤ X₀} {l₁ : Y₁ ⥤ X₁} {l₂ : Y₂ ⥤ X₂}
    {f₀ : X₀ ⥤ Y₀} {f₁ : X₁ ⥤ Y₁} {f₂ : X₂ ⥤ Y₂}
    (A₀ : l₀ ⊣ f₀) (A₁ : l₁ ⊣ f₁) (A₂ : l₂ ⊣ f₂)
    (e₁ : aY ⋙ l₁ ≅ l₀ ⋙ aX) (e₂ : bY ⋙ l₂ ≅ l₁ ⋙ bX)
    (e₃ : cY ⋙ l₂ ≅ l₀ ⋙ cX)
    (βX : aX ⋙ bX ≅ cX) (βY : aY ⋙ bY ≅ cY)
    (ρ₁ : f₀ ⋙ aY ⟶ aX ⋙ f₁) (ρ₂ : f₁ ⋙ bY ⟶ bX ⋙ f₂)
    (ρ₃ : f₀ ⋙ cY ⟶ cX ⋙ f₂)
    (h₁ : ∀ K, l₁.map (ρ₁.app K) ≫ A₁.counit.app (aX.obj K) =
      e₁.hom.app (f₀.obj K) ≫ aX.map (A₀.counit.app K))
    (h₂ : ∀ K, l₂.map (ρ₂.app K) ≫ A₂.counit.app (bX.obj K) =
      e₂.hom.app (f₁.obj K) ≫ bX.map (A₁.counit.app K))
    (h₃ : ∀ K, l₂.map (ρ₃.app K) ≫ A₂.counit.app (cX.obj K) =
      e₃.hom.app (f₀.obj K) ≫ cX.map (A₀.counit.app K))
    (hp : ∀ K, e₂.hom.app (aY.obj K) ≫ bX.map (e₁.hom.app K) ≫
      βX.hom.app (l₀.obj K) = l₂.map (βY.hom.app K) ≫ e₃.hom.app K)
    (K : X₀) :
    βY.hom.app (f₀.obj K) ≫ ρ₃.app K =
      bY.map (ρ₁.app K) ≫ ρ₂.app (aX.obj K) ≫ f₂.map (βX.hom.app K) := by
  apply (A₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := A₂.counit.naturality (βX.hom.app K)
  change l₂.map (f₂.map (βX.hom.app K)) ≫ A₂.counit.app _ =
    A₂.counit.app _ ≫ βX.hom.app K at hn
  rw [hn, h₃, reassoc_of% (h₂ (aX.obj K))]
  have hl := e₂.hom.naturality (ρ₁.app K)
  change l₂.map (bY.map (ρ₁.app K)) ≫ e₂.hom.app _ =
    e₂.hom.app _ ≫ bX.map (l₁.map (ρ₁.app K)) at hl
  dsimp only [Functor.comp_obj] at hl
  rw [← Category.assoc, ← Category.assoc, hl]
  simp only [Category.assoc]
  rw [← bX.map_comp_assoc, h₁, Functor.map_comp]
  have hb := βX.hom.naturality (A₀.counit.app K)
  change bX.map (aX.map (A₀.counit.app K)) ≫ βX.hom.app K =
    βX.hom.app _ ≫ cX.map (A₀.counit.app K) at hb
  dsimp only [Functor.comp_obj] at hb
  simp only [Category.assoc]
  rw [hb]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ cX.map (A₀.counit.app K)) (hp (f₀.obj K)).symm

private theorem scalar_mate_pasting
    (a : Λ₀ ⟶ Λ₁) [IsMonHom a] (b : Λ₁ ⟶ Λ₂) [IsMonHom b]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l01 : D a Y ⋙ L Λ₁ f ≅ L Λ₀ f ⋙ D a X)
    (l12 : D b Y ⋙ L Λ₂ f ≅ L Λ₁ f ⋙ D b X)
    (l02 : D (a ≫ b) Y ⋙ L Λ₂ f ≅ L Λ₀ f ⋙ D (a ≫ b) X)
    (betaX : D a X ⋙ D b X ≅ D (a ≫ b) X)
    (betaY : D a Y ⋙ D b Y ≅ D (a ≫ b) Y)
    (hp : ∀ K : DerivedCategory (Modules Λ₀ Y),
      l12.hom.app ((D a Y).obj K) ≫ (D b X).map (l01.hom.app K) ≫
        betaX.hom.app ((L Λ₀ f).obj K) =
        (L Λ₂ f).map (betaY.hom.app K) ≫ l02.hom.app K)
    (K : DerivedCategory (Modules Λ₀ X)) :
    betaY.hom.app ((F Λ₀ f).obj K) ≫ (rho (a ≫ b) f l02).app K =
      (D b Y).map ((rho a f l01).app K) ≫
        (rho b f l12).app ((D a X).obj K) ≫
        (F Λ₂ f).map (betaX.hom.app K) := by
  exact mate_rectangle (adj Λ₀ f) (adj Λ₁ f) (adj Λ₂ f) l01 l12 l02 betaX betaY
    (rho a f l01) (rho b f l12) (rho (a ≫ b) f l02)
    (rho_counit a f l01) (rho_counit b f l12) (rho_counit (a ≫ b) f l02) hp K

/-- Normalized successive scalar extension, its units and transposes, and its geometric
pullback and direct-image pastings. The comparison `SuccessiveNormalized` includes
both representative formulas by the ordinary balanced scalar-composition isomorphism.
The three balancing isomorphisms are arbitrary normalized ones, so these identities
hold for the specified comparisons independently of representative choices. -/
theorem internal_scalar_mate_transitivity
    (a : Λ₀ ⟶ Λ₁) [IsMonHom a] (b : Λ₁ ⟶ Λ₂) [IsMonHom b]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l01 : D a Y ⋙ L Λ₁ f ≅ L Λ₀ f ⋙ D a X)
    (l12 : D b Y ⋙ L Λ₂ f ≅ L Λ₁ f ⋙ D b X)
    (l02 : D (a ≫ b) Y ⋙ L Λ₂ f ≅ L Λ₀ f ⋙ D (a ≫ b) X)
    (h01 : PullNormalized a f l01) (h12 : PullNormalized b f l12)
    (h02 : PullNormalized (a ≫ b) f l02) :
    ∃ (betaX : D a X ⋙ D b X ≅ D (a ≫ b) X)
      (betaY : D a Y ⋙ D b Y ≅ D (a ≫ b) Y),
      SuccessiveNormalized a b (a ≫ b) rfl X betaX ∧
      SuccessiveNormalized a b (a ≫ b) rfl Y betaY ∧
      (∀ K : DerivedCategory (Modules Λ₀ X),
        (scalarAdj a X).unit.app K ≫
          (V a X).map ((scalarAdj b X).unit.app ((D a X).obj K)) ≫
          (V a X).map ((V b X).map (betaX.hom.app K)) ≫
          (scalarRestrictionComp a b X).hom.app ((D (a ≫ b) X).obj K) =
        (scalarAdj (a ≫ b) X).unit.app K) ∧
      (∀ K : DerivedCategory (Modules Λ₀ Y),
        (scalarAdj a Y).unit.app K ≫
          (V a Y).map ((scalarAdj b Y).unit.app ((D a Y).obj K)) ≫
          (V a Y).map ((V b Y).map (betaY.hom.app K)) ≫
          (scalarRestrictionComp a b Y).hom.app ((D (a ≫ b) Y).obj K) =
        (scalarAdj (a ≫ b) Y).unit.app K) ∧
      (∀ (K : DerivedCategory (Modules Λ₀ X))
          (H : DerivedCategory (Modules Λ₂ X)) (g : K ⟶ (V (a ≫ b) X).obj H),
        ((scalarAdj a X).comp (scalarAdj b X)).homEquiv K H
          (betaX.hom.app K ≫ ((scalarAdj (a ≫ b) X).homEquiv K H).symm g) =
        g ≫ (scalarRestrictionComp a b X).inv.app H) ∧
      (∀ (K : DerivedCategory (Modules Λ₀ Y))
          (H : DerivedCategory (Modules Λ₂ Y)) (g : K ⟶ (V (a ≫ b) Y).obj H),
        ((scalarAdj a Y).comp (scalarAdj b Y)).homEquiv K H
          (betaY.hom.app K ≫ ((scalarAdj (a ≫ b) Y).homEquiv K H).symm g) =
        g ≫ (scalarRestrictionComp a b Y).inv.app H) ∧
      (∀ K : DerivedCategory (Modules Λ₀ Y),
        l12.hom.app ((D a Y).obj K) ≫ (D b X).map (l01.hom.app K) ≫
            betaX.hom.app ((L Λ₀ f).obj K) =
          (L Λ₂ f).map (betaY.hom.app K) ≫ l02.hom.app K) ∧
      (∀ K : DerivedCategory (Modules Λ₀ X),
        betaY.hom.app ((F Λ₀ f).obj K) ≫ (rho (a ≫ b) f l02).app K =
          (D b Y).map ((rho a f l01).app K) ≫
            (rho b f l12).app ((D a X).obj K) ≫
            (F Λ₂ f).map (betaX.hom.app K)) := by
  refine ⟨scalarComp a b X, scalarComp a b Y, scalarComp_normalized a b X,
    scalarComp_normalized a b Y, scalarComp_unit a b X, scalarComp_unit a b Y,
    scalarComp_transpose a b X, scalarComp_transpose a b Y, ?_, ?_⟩
  · exact scalar_pull_paste a b f l01 l12 l02 h01 h12 h02
  · exact scalar_mate_pasting a b f l01 l12 l02 (scalarComp a b X) (scalarComp a b Y)
      (scalar_pull_paste a b f l01 l12 l02 h01 h12 h02)

end AlgebraicGeometry.ProEtale.QuotientChange
