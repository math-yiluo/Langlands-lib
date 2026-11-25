/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! # Multiplication units for derived coefficient extension

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E and 07A6
(blueprint: lem-pur-coefficient-scalar-units).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped ChangeOfRings
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}

variable {p : Scalars.{c, v, r} J}
  (n : _root_.SheafOfModules.SuccessiveDerivedQuotient.Normalization.{c, v, r,
    max c v (r + 1)} (J := J) p)

private theorem termwise_commShift
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (t : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapHomologicalComplex t (.up ℤ)) ℤ := by
  constructor
  intro n
  ext K i
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    NatTrans.mapHomologicalComplex_app_f, CochainComplex.shiftFunctor_map_f',
    CochainComplex.shiftFunctor_obj_X', Category.id_comp, Category.comp_id]

private theorem homotopy_commShift
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (t : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapHomotopyCategory t (.up ℤ)) ℤ := by
  have := termwise_commShift t
  have he : whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (NatTrans.mapHomotopyCategory t (.up ℤ)) =
      (F.mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ))
          (HomotopyCategory.quotient B (.up ℤ)) ≫
        (G.mapHomotopyCategoryFactors (.up ℤ)).inv := by
    ext K
    simp only [Functor.comp_obj, Functor.whiskerLeft_app,
      NatTrans.mapHomotopyCategory_app, NatTrans.comp_app, Functor.whiskerRight_app]
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    erw [Category.id_comp, Category.comp_id]
    rfl
  have : NatTrans.CommShift (whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (NatTrans.mapHomotopyCategory t (.up ℤ))) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient A (.up ℤ))
    (fun K ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective K).choose_spec ▸
      inferInstance⟩)

private theorem homotopyId_commShift
    {A : Type*} [Category A] [Preadditive A] :
    NatTrans.CommShift (Functor.mapHomotopyCategoryIdIso A (.up ℤ)).hom ℤ := by
  have hc : NatTrans.CommShift (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom ℤ := by
    constructor
    intro n
    ext K i
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.commShiftIso_id_hom_app, HomologicalComplex.id_f,
      CochainComplex.shiftFunctor_map_f', mapHomologicalComplexIdIso_hom_app_f,
      Category.id_comp]
    erw [Category.id_comp]
    rfl
  have he : whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (Functor.mapHomotopyCategoryIdIso A (.up ℤ)).hom =
      ((𝟭 A).mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        whiskerRight (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom
          (HomotopyCategory.quotient A (.up ℤ)) ≫
        (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv := by
    ext K
    simp only [Functor.comp_obj, Functor.id_obj, Functor.whiskerLeft_app,
      mapHomotopyCategoryIdIso_hom_app, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Category.comp_id]
    erw [Category.id_comp]
  have : NatTrans.CommShift (whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (Functor.mapHomotopyCategoryIdIso A (.up ℤ)).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient A (.up ℤ))
    (fun K ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective K).choose_spec ▸
      inferInstance⟩)

private def restrictionUnit (R : Sheaf J CommRingCat.{r}) :
    _root_.SheafOfModules.SuccessiveDerivedQuotient.restriction.{c, v, r} (𝟙 R) ≅ 𝟭 (Mod J R) :=
  NatIso.ofComponents (fun M ↦ {
    hom := { val := {
      app := fun U ↦ ModuleCat.ofHom {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    inv := { val := {
      app := fun U ↦ ModuleCat.ofHom {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } } }) (by intros; ext; rfl)

private def ordinaryUnit (R : Sheaf J CommRingCat.{r}) :
    (p (𝟙 R)).ordinary ≅ 𝟭 (Mod J R) := by
  let a := (n.ordinaryAdjunction (𝟙 R)).ofNatIsoRight (restrictionUnit R)
  exact a.leftAdjointUniq (Adjunction.id)

private def homotopyUnit (R : Sheaf J CommRingCat.{r}) :
    (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ≅
      𝟭 (HomotopyCategory (Mod J R) (.up ℤ)) :=
  { hom := NatTrans.mapHomotopyCategory (ordinaryUnit n R).hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory (ordinaryUnit n R).inv (.up ℤ)
    hom_inv_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] } ≪≫
    Functor.mapHomotopyCategoryIdIso (Mod J R) (.up ℤ)

private def homotopyUnitQ (R : Sheaf J CommRingCat.{r}) :
    (p (𝟙 R)).ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Qh :=
  isoWhiskerRight (homotopyUnit n R) DerivedCategory.Qh ≪≫
    Functor.leftUnitor DerivedCategory.Qh

private def derivedUnit (R : Sheaf J CommRingCat.{r}) :
    (p (𝟙 R)).derived ≅ 𝟭 (D J R) := by
  let a : DerivedCategory.Qh ⋙ 𝟭 (D J R) ≅ DerivedCategory.Qh :=
    Functor.rightUnitor DerivedCategory.Qh
  let := (p (𝟙 R)).universal
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Mod J R) (.up ℤ)) (𝟭 (D J R)) a
  exact Functor.leftDerivedNatIso _ _ (p (𝟙 R)).counit a.hom
    (HomotopyCategory.quasiIso (Mod J R) (.up ℤ)) (homotopyUnitQ n R)

private theorem derivedUnit_app_homotopy (R : Sheaf J CommRingCat.{r})
    (H : HomotopyCategory (Mod J R) (.up ℤ)) :
    (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) =
      (p (𝟙 R)).counit.app H ≫
        DerivedCategory.Qh.map ((homotopyUnit n R).hom.app H) := by
  let a : DerivedCategory.Qh ⋙ 𝟭 (D J R) ≅ DerivedCategory.Qh :=
    Functor.rightUnitor DerivedCategory.Qh
  let := (p (𝟙 R)).universal
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Mod J R) (.up ℤ)) (𝟭 (D J R)) a
  have h := Functor.leftDerivedNatTrans_app (p (𝟙 R)).derived (𝟭 (D J R))
    (p (𝟙 R)).counit a.hom (HomotopyCategory.quasiIso (Mod J R) (.up ℤ))
    (homotopyUnitQ n R).hom H
  change (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) ≫ 𝟙 _ = _ at h
  change (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) ≫ 𝟙 _ =
    (p (𝟙 R)).counit.app H ≫
      (DerivedCategory.Qh.map ((homotopyUnit n R).hom.app H) ≫ 𝟙 _) at h
  simpa only [Category.comp_id] using h

private theorem derivedUnit_commShift
    [scalar : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
      (p a).derived.CommShift ℤ]
    (canonical : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
      NatTrans.CommShift (p a).counit ℤ) (R : Sheaf J CommRingCat.{r}) :
    NatTrans.CommShift (derivedUnit n R).hom ℤ := by
  have := homotopy_commShift (ordinaryUnit n R).hom
  have := homotopyId_commShift (A := Mod J R)
  have : NatTrans.CommShift (homotopyUnit n R).hom ℤ := by
    dsimp only [homotopyUnit, Iso.trans_hom]
    infer_instance
  have : NatTrans.CommShift (homotopyUnitQ n R).hom ℤ := by
    change NatTrans.CommShift
      (whiskerRight (homotopyUnit n R).hom DerivedCategory.Qh ≫
        (Functor.leftUnitor _).hom) ℤ
    infer_instance
  have := canonical (𝟙 R)
  have he : whiskerLeft DerivedCategory.Qh (derivedUnit n R).hom =
      (p (𝟙 R)).counit ≫ (homotopyUnitQ n R).hom ≫
        (Functor.rightUnitor DerivedCategory.Qh).inv := by
    ext H
    change (derivedUnit n R).hom.app (DerivedCategory.Qh.obj H) =
      (p (𝟙 R)).counit.app H ≫
        (DerivedCategory.Qh.map ((homotopyUnit n R).hom.app H) ≫ 𝟙 _) ≫ 𝟙 _
    simp only [Category.comp_id]
    exact derivedUnit_app_homotopy n R H
  have : NatTrans.CommShift
      (whiskerLeft DerivedCategory.Qh (derivedUnit n R).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun H ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso H).inv, inferInstance⟩)

include n

end SheafOfModules.RingedCoefficientProjection
