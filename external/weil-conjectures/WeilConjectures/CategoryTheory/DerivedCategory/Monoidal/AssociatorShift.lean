/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftUnitor
public import WeilConjectures.Mathlib.Algebra.Homology.MonoidalShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# The associator of the derived tensor product commutes with shifts

For objects `K`, `L`, `M` of the derived category `D(C)` and `a b c : ℤ`, the identifications
`X⟦a⟧ ⊗ᴸ Y⟦b⟧ ≅ (X ⊗ᴸ Y)⟦a + b⟧` (`DerivedCategory.shiftTensorShiftIso`) are compatible with the
associator: the two isomorphisms `(K⟦a⟧ ⊗ᴸ L⟦b⟧) ⊗ᴸ M⟦c⟧ ≅ (K ⊗ᴸ (L ⊗ᴸ M))⟦a + b + c⟧` obtained
by moving the shifts out before or after applying the associator agree
(`DerivedCategory.shiftTensorShiftIso_assoc`). No sign appears.

## Strategy

The associator, viewed as a natural transformation in one of the three variables
(`CategoryTheory.MonoidalCategory.associatorNatTrans₁`, `associatorNatTrans₂`,
`associatorNatTrans₃`), commutes with the shifts. For the other two variables in the image of
K-flat complexes, this is checked through the localization functor
`CochainComplex C ℤ ⥤ D(C)`: there the associator of `D(C)` is identified with the associator of
cochain complexes by the comparisons `L P ⊗ᴸ L Z ≅ L (P ⊗ Z)`, which commute with shifts, and
the associator of cochain complexes commutes with shifts
(`CochainComplex.associator_hom_comp_mapBifunctorShift₁Iso_hom` and its variants). Every object
is isomorphic to the image of a K-flat complex, and the statement is invariant under
isomorphisms (`CategoryTheory.MonoidalCategory.commShift_associatorNatTrans₁_of_iso`, ...).
The compatibility with `DerivedCategory.shiftTensorShiftIso` is then a formal consequence.

## Main statements

- `DerivedCategory.shiftTensorShiftIso_assoc`
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

universe w v u

namespace CategoryTheory.MonoidalCategory

variable (D : Type*) [Category D] [MonoidalCategory D]

/-- The associator `(X ⊗ Y) ⊗ Z ⟶ X ⊗ (Y ⊗ Z)`, natural in `X`. -/
@[simps]
def associatorNatTrans₁ (Y Z : D) :
    (curriedTensor D).flip.obj Y ⋙ (curriedTensor D).flip.obj Z ⟶
      (curriedTensor D).flip.obj (Y ⊗ Z) where
  app X := (α_ X Y Z).hom

/-- The associator `(X ⊗ Y) ⊗ Z ⟶ X ⊗ (Y ⊗ Z)`, natural in `Y`. -/
@[simps]
def associatorNatTrans₂ (X Z : D) :
    (curriedTensor D).obj X ⋙ (curriedTensor D).flip.obj Z ⟶
      (curriedTensor D).flip.obj Z ⋙ (curriedTensor D).obj X where
  app Y := (α_ X Y Z).hom

/-- The associator `(X ⊗ Y) ⊗ Z ⟶ X ⊗ (Y ⊗ Z)`, natural in `Z`. -/
@[simps]
def associatorNatTrans₃ (X Y : D) :
    (curriedTensor D).obj (X ⊗ Y) ⟶ (curriedTensor D).obj Y ⋙ (curriedTensor D).obj X where
  app Z := (α_ X Y Z).hom

section Shift

variable {D} [HasShift D ℤ] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [(curriedTensor D).CommShift₂Int]

lemma commShift_associatorNatTrans₁_of_iso {Y Z Y' Z' : D} (eY : Y ≅ Y') (eZ : Z ≅ Z')
    [NatTrans.CommShift (associatorNatTrans₁ D Y Z) ℤ] :
    NatTrans.CommShift (associatorNatTrans₁ D Y' Z') ℤ := by
  have : associatorNatTrans₁ D Y' Z' =
      Functor.whiskerRight ((curriedTensor D).flip.map eY.inv) ((curriedTensor D).flip.obj Z') ≫
        Functor.whiskerLeft ((curriedTensor D).flip.obj Y) ((curriedTensor D).flip.map eZ.inv) ≫
        associatorNatTrans₁ D Y Z ≫ (curriedTensor D).flip.map (eY.hom ⊗ₘ eZ.hom) := by
    ext X
    simp [tensorHom_def']
  rw [this]
  infer_instance

lemma commShift_associatorNatTrans₂_of_iso {X Z X' Z' : D} (eX : X ≅ X') (eZ : Z ≅ Z')
    [NatTrans.CommShift (associatorNatTrans₂ D X Z) ℤ] :
    NatTrans.CommShift (associatorNatTrans₂ D X' Z') ℤ := by
  have : associatorNatTrans₂ D X' Z' =
      Functor.whiskerRight ((curriedTensor D).map eX.inv) ((curriedTensor D).flip.obj Z') ≫
        Functor.whiskerLeft ((curriedTensor D).obj X) ((curriedTensor D).flip.map eZ.inv) ≫
        associatorNatTrans₂ D X Z ≫
        Functor.whiskerRight ((curriedTensor D).flip.map eZ.hom) ((curriedTensor D).obj X) ≫
        Functor.whiskerLeft ((curriedTensor D).flip.obj Z') ((curriedTensor D).map eX.hom) := by
    ext Y
    simp
  rw [this]
  infer_instance

lemma commShift_associatorNatTrans₃_of_iso {X Y X' Y' : D} (eX : X ≅ X') (eY : Y ≅ Y')
    [NatTrans.CommShift (associatorNatTrans₃ D X Y) ℤ] :
    NatTrans.CommShift (associatorNatTrans₃ D X' Y') ℤ := by
  have : associatorNatTrans₃ D X' Y' =
      (curriedTensor D).map (eX.inv ⊗ₘ eY.inv) ≫ associatorNatTrans₃ D X Y ≫
        Functor.whiskerRight ((curriedTensor D).map eY.hom) ((curriedTensor D).obj X) ≫
        Functor.whiskerLeft ((curriedTensor D).obj Y') ((curriedTensor D).map eX.hom) := by
    ext Z
    simp only [Functor.comp_obj, curriedTensor_obj_obj, NatTrans.comp_app, curriedTensor_map_app,
      associatorNatTrans₃_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      curriedTensor_obj_map, tensorHom_def, comp_whiskerRight, assoc,
      associator_naturality_middle_assoc]
    simp
  rw [this]
  infer_instance

/-- Prove shift coherence with abstract structures, avoiding reduction of the derived tensor. -/
private lemma commShiftIso_assoc_aux (K L M : D) (b c : ℤ)
    [NatTrans.CommShift (associatorNatTrans₂ D K (M⟦c⟧)) ℤ]
    [NatTrans.CommShift (associatorNatTrans₃ D K L) ℤ] :
    (((curriedTensor D).obj K).commShiftIso b).hom.app L ▷ M⟦c⟧ ≫
      (((curriedTensor D).flip.obj (M⟦c⟧)).commShiftIso b).hom.app (K ⊗ L) ≫
      ((((curriedTensor D).obj (K ⊗ L)).commShiftIso c).hom.app M ≫
        (α_ K L M).hom⟦c⟧')⟦b⟧' =
    (α_ K (L⟦b⟧) (M⟦c⟧)).hom ≫ K ◁ ((((curriedTensor D).flip.obj (M⟦c⟧)).commShiftIso b).app L ≪≫
        (shiftFunctor D b).mapIso ((((curriedTensor D).obj L).commShiftIso c).app M) ≪≫
        (shiftFunctorAdd' D c b (b + c) (add_comm c b)).symm.app _).hom ≫
      (((curriedTensor D).obj K).commShiftIso (b + c)).hom.app (L ⊗ M) ≫
      (shiftFunctorAdd' D c b (b + c) (add_comm c b)).hom.app (K ⊗ (L ⊗ M)) := by
  have h₂ := NatTrans.shift_app_comm (associatorNatTrans₂ D K (M⟦c⟧)) b L
  have h₃ := NatTrans.shift_app_comm (associatorNatTrans₃ D K L) c M
  simp only [Functor.commShiftIso_comp_hom_app, associatorNatTrans₂_app,
    associatorNatTrans₃_app, Functor.comp_obj, Functor.flip_obj_map, curriedTensor_map_app,
    curriedTensor_obj_map, curriedTensor_obj_obj, Functor.flip_obj_obj, assoc] at h₂ h₃
  rw [h₃, Functor.map_comp, Functor.map_comp, reassoc_of% h₂]
  rw [Functor.commShiftIso_add' ((curriedTensor D).obj K)
    (show c + b = b + c from add_comm c b)]
  simp only [Functor.CommShift.isoAdd'_hom_app, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, curriedTensor_obj_map, assoc,
    MonoidalCategory.whiskerLeft_comp]
  congr 2
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    assoc]
  erw [Iso.inv_hom_id_app]
  erw [comp_id]
  erw [Iso.inv_hom_id_app]
  erw [comp_id]
  have := ((curriedTensor D).obj K).commShiftIso_hom_naturality_assoc
    ((((curriedTensor D).obj L).commShiftIso c).hom.app M) b
    (((((curriedTensor D).obj K).commShiftIso c).hom.app (L ⊗ M))⟦b⟧')
  exact this.symm

end Shift

end CategoryTheory.MonoidalCategory

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

local instance hasColimitsOfSize_associatorShift : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

namespace TensorCommShift₂

instance (K L : CochainComplex C ℤ) :
    NatTrans.CommShift (associatorNatTrans₃ (CochainComplex C ℤ) K L) ℤ where
  shift_comm n := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app, associatorNatTrans₃_app]
    exact (CochainComplex.associator_hom_comp_whiskerLeft_mapBifunctorShift₂Iso_hom K L M n).symm

instance (K L : CochainComplex C ℤ) :
    NatTrans.CommShift (associatorNatTrans₁ (CochainComplex C ℤ) K L) ℤ where
  shift_comm n := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app, associatorNatTrans₁_app, Functor.flip_obj_map,
      curriedTensor_map_app, assoc]
    exact (CochainComplex.associator_hom_comp_mapBifunctorShift₁Iso_hom M K L n).symm

instance (K M : CochainComplex C ℤ) :
    NatTrans.CommShift (associatorNatTrans₂ (CochainComplex C ℤ) K M) ℤ where
  shift_comm n := by
    refine NatTrans.ext (funext fun L ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app, associatorNatTrans₂_app, Functor.flip_obj_map,
      curriedTensor_map_app, curriedTensor_obj_map, assoc]
    exact (CochainComplex.associator_hom_comp_whiskerLeft_mapBifunctorShift₁Iso_hom K L M n).symm

variable {C}

/-- For a K-flat complex `P`, the comparison `L P ⊗ᴸ L Z ≅ L (P ⊗ Z)`, natural in `Z`. -/
noncomputable def tensorLeftLift (P : CochainComplex.KFlat C) :
    L C ⋙ (curriedTensor (DerivedCategory C)).obj ((LKFlat C).obj P) ⟶
      (curriedTensor (CochainComplex C ℤ)).obj P.obj ⋙ L C :=
  Functor.CommShift₂OfLocalization.liftingIsoApp (LKFlat C) (L C)
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ)) (F C)
    (curriedTensor (DerivedCategory C)) P

instance (P : CochainComplex.KFlat C) : NatTrans.CommShift (tensorLeftLift P) ℤ :=
  Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (LKFlat C) (L C)
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ)) (F C)
    (curriedTensor (DerivedCategory C)) P

instance (P : CochainComplex.KFlat C) : IsIso (tensorLeftLift P) := by
  dsimp [tensorLeftLift, Functor.CommShift₂OfLocalization.liftingIsoApp]
  infer_instance

lemma tensorLeftLift_app (P : CochainComplex.KFlat C) (Z : CochainComplex C ℤ) :
    (tensorLeftLift P).app Z = Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient _ _).obj P.obj)
      ((HomotopyCategory.quotient _ _).obj Z) := rfl

instance (Q : CochainComplex.KFlat C) :
    NatTrans.CommShift (tensorRightCounit ((HomotopyCategory.quotient C (.up ℤ)).obj Q.obj)) ℤ := by
  have hQ := (HomotopyCategory.kFlat_quotient_obj_iff _).2 Q.2
  have e := commShiftTensorRight_eq C Q
  let := commShiftTensorRightQhObj ((HomotopyCategory.quotient C _).obj Q.obj) hQ
  have := isIso_tensorRightCounit ((HomotopyCategory.quotient C _).obj Q.obj) hQ
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((curriedTensor _).flip.obj ((HomotopyCategory.quotient C _).obj Q.obj) ⋙ Qh)
      ((curriedTensor _).flip.obj (Qh.obj ((HomotopyCategory.quotient C _).obj Q.obj))) :=
    ⟨asIso (tensorRightCounit _)⟩
  have h := NatTrans.commShift_iso_hom_of_localization Qh (HomotopyCategory.quasiIso C (.up ℤ)) ℤ
    ((curriedTensor _).flip.obj ((HomotopyCategory.quotient C _).obj Q.obj) ⋙ Qh)
    ((curriedTensor (DerivedCategory C)).flip.obj
      (Qh.obj ((HomotopyCategory.quotient C _).obj Q.obj)))
  have h' : NatTrans.CommShift
      (tensorRightCounit ((HomotopyCategory.quotient C _).obj Q.obj)) ℤ := h
  convert h'
  exact e

/-- For a K-flat complex `Q`, the comparison `L Z ⊗ᴸ L Q ≅ L (Z ⊗ Q)`, natural in `Z`. -/
noncomputable def tensorRightLift (Q : CochainComplex.KFlat C) :
    L C ⋙ (curriedTensor (DerivedCategory C)).flip.obj ((LKFlat C).obj Q) ⟶
      (curriedTensor (CochainComplex C ℤ)).flip.obj Q.obj ⋙ L C :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (tensorRightCounit ((HomotopyCategory.quotient C (.up ℤ)).obj Q.obj)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((curriedTensor C).quotientCompBifunctorMapHomotopyFlipObjIso
      (.up ℤ) (.up ℤ) (.up ℤ) Q.obj).hom Qh ≫
    (Functor.associator _ _ _).hom

instance (Q : CochainComplex.KFlat C) : NatTrans.CommShift (tensorRightLift Q) ℤ := by
  dsimp only [tensorRightLift]
  infer_instance

instance (Q : CochainComplex.KFlat C) : IsIso (tensorRightLift Q) := by
  have := isIso_tensorRightCounit ((HomotopyCategory.quotient C _).obj Q.obj)
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 Q.2)
  dsimp only [tensorRightLift]
  infer_instance

lemma tensorRightLift_app (Q : CochainComplex.KFlat C) (Z : CochainComplex C ℤ) :
    (tensorRightLift Q).app Z = Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient _ _).obj Z)
      ((HomotopyCategory.quotient _ _).obj Q.obj) := by
  simp only [tensorRightLift, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, comp_id,
    id_comp]
  rw [show ((curriedTensor C).quotientCompBifunctorMapHomotopyFlipObjIso
    (.up ℤ) (.up ℤ) (.up ℤ) Q.obj).hom = 𝟙 _ from rfl]
  erw [CategoryTheory.Functor.map_id, comp_id]
  rfl

/-- The tensor product of two K-flat complexes, as a K-flat complex. -/
noncomputable def kFlatTensor (P Q : CochainComplex.KFlat C) : CochainComplex.KFlat C :=
  ⟨P.obj ⊗ Q.obj, ObjectProperty.prop_tensor P.2 Q.2⟩

omit [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))] in
/-- The quotient functor to the homotopy category maps the associator of cochain complexes
to the associator of the homotopy category. -/
lemma quotient_map_associator_hom (K₁ K₂ K₃ : CochainComplex C ℤ) :
    (HomotopyCategory.quotient C (.up ℤ)).map (α_ K₁ K₂ K₃).hom =
      (α_ ((HomotopyCategory.quotient C (.up ℤ)).obj K₁)
        ((HomotopyCategory.quotient C (.up ℤ)).obj K₂)
        ((HomotopyCategory.quotient C (.up ℤ)).obj K₃)).hom :=
  (HomotopyCategory.MonoidalCategory.associator_hom_app_app_app K₁ K₂ K₃).symm

omit [Abelian.HasFunctorialFlatResolution C] in
/-- The associativity of the comparisons `L K ⊗ᴸ L K' ⟶ L (K ⊗ K')`. -/
lemma μ_associativity (K₁ K₂ K₃ : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient C (.up ℤ)).obj K₁)
        ((HomotopyCategory.quotient C (.up ℤ)).obj K₂) ▷ (L C).obj K₃ ≫
      Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient C (.up ℤ)).obj (K₁ ⊗ K₂))
        ((HomotopyCategory.quotient C (.up ℤ)).obj K₃) ≫ (L C).map (α_ K₁ K₂ K₃).hom =
    (α_ ((L C).obj K₁) ((L C).obj K₂) ((L C).obj K₃)).hom ≫
      (L C).obj K₁ ◁ Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient C (.up ℤ)).obj K₂)
        ((HomotopyCategory.quotient C (.up ℤ)).obj K₃) ≫
      Functor.LaxMonoidal.μ Qh ((HomotopyCategory.quotient C (.up ℤ)).obj K₁)
        ((HomotopyCategory.quotient C (.up ℤ)).obj (K₂ ⊗ K₃)) := by
  have h := Functor.LaxMonoidal.associativity Qh ((HomotopyCategory.quotient C (.up ℤ)).obj K₁)
    ((HomotopyCategory.quotient C (.up ℤ)).obj K₂) ((HomotopyCategory.quotient C (.up ℤ)).obj K₃)
  rw [← quotient_map_associator_hom] at h
  exact h

omit [IsGrothendieckAbelian C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))] in
/-- Every object of `D(C)` maps isomorphically to the image of a cochain complex. -/
lemma essSurj_L (X : DerivedCategory C) : ∃ (Y : CochainComplex C ℤ) (f : X ⟶ (L C).obj Y),
    IsIso f := by
  have := Localization.essSurj (L C) (HomologicalComplex.quasiIso C (.up ℤ))
  exact ⟨_, ((L C).objObjPreimageIso X).inv, inferInstance⟩

omit [IsGrothendieckAbelian C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))] in
/-- A natural transformation `τ : G₁ ⟶ G₂` of endofunctors of `D(C)` commutes with the shifts
if, through the localization functor, it is identified with a natural transformation which
does. -/
lemma commShift_of_whiskerLeft_L {G₁ G₂ : DerivedCategory C ⥤ DerivedCategory C}
    [G₁.CommShift ℤ] [G₂.CommShift ℤ] (τ : G₁ ⟶ G₂) {H₁ H₂ : CochainComplex C ℤ ⥤ DerivedCategory C}
    [H₁.CommShift ℤ] [H₂.CommShift ℤ] (e₁ : L C ⋙ G₁ ⟶ H₁) (e₂ : L C ⋙ G₂ ⟶ H₂) (σ : H₁ ⟶ H₂)
    [NatTrans.CommShift e₁ ℤ] [NatTrans.CommShift e₂ ℤ] [IsIso e₂] [NatTrans.CommShift σ ℤ]
    (he : Functor.whiskerLeft (L C) τ ≫ e₂ = e₁ ≫ σ) : NatTrans.CommShift τ ℤ := by
  have : NatTrans.CommShift (Functor.whiskerLeft (L C) τ) ℤ := by
    have : Functor.whiskerLeft (L C) τ = e₁ ≫ σ ≫ inv e₂ := by
      rw [← reassoc_of% he, IsIso.hom_inv_id, comp_id]
    rw [this]
    have : NatTrans.CommShift (inv e₂) ℤ := NatTrans.CommShift.of_isIso _ _
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (L C) (fun X ↦ by
    obtain ⟨Y, f, hf⟩ := essSurj_L X
    exact ⟨Y, f, inferInstance⟩)

lemma commShift_associatorNatTrans₃_kFlat (P Q : CochainComplex.KFlat C) :
    NatTrans.CommShift (associatorNatTrans₃ (DerivedCategory C) ((LKFlat C).obj P)
      ((LKFlat C).obj Q)) ℤ := by
  refine commShift_of_whiskerLeft_L _
    (Functor.whiskerLeft (L C) ((curriedTensor (DerivedCategory C)).map
      ((tensorLeftLift P).app Q.obj)) ≫ tensorLeftLift (kFlatTensor P Q))
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (tensorLeftLift Q) ((curriedTensor (DerivedCategory C)).obj
        ((LKFlat C).obj P)) ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((curriedTensor (CochainComplex C ℤ)).obj Q.obj) (tensorLeftLift P) ≫
      (Functor.associator _ _ _).inv)
    (Functor.whiskerRight (associatorNatTrans₃ (CochainComplex C ℤ) P.obj Q.obj) (L C)) ?_
  ext Z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, associatorNatTrans₃_app,
    tensorLeftLift_app, comp_id, id_comp, curriedTensor_obj_map, curriedTensor_map_app, assoc]
  exact (μ_associativity P.obj Q.obj Z).symm

lemma commShift_associatorNatTrans₁_kFlat (Q R : CochainComplex.KFlat C) :
    NatTrans.CommShift (associatorNatTrans₁ (DerivedCategory C) ((LKFlat C).obj Q)
      ((LKFlat C).obj R)) ℤ := by
  refine commShift_of_whiskerLeft_L _
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (tensorRightLift Q) ((curriedTensor (DerivedCategory C)).flip.obj
        ((LKFlat C).obj R)) ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((curriedTensor (CochainComplex C ℤ)).flip.obj Q.obj)
        (tensorRightLift R) ≫
      (Functor.associator _ _ _).inv)
    (Functor.whiskerLeft (L C) ((curriedTensor (DerivedCategory C)).flip.map
      ((tensorLeftLift Q).app R.obj)) ≫ tensorRightLift (kFlatTensor Q R))
    (Functor.whiskerRight (associatorNatTrans₁ (CochainComplex C ℤ) Q.obj R.obj) (L C)) ?_
  ext Z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, associatorNatTrans₁_app,
    tensorLeftLift_app, tensorRightLift_app, id_comp, curriedTensor_obj_map,
    curriedTensor_map_app, Functor.flip_obj_map, Functor.flip_map_app, assoc]
  exact (μ_associativity Z Q.obj R.obj).symm

lemma commShift_associatorNatTrans₂_kFlat (P R : CochainComplex.KFlat C) :
    NatTrans.CommShift (associatorNatTrans₂ (DerivedCategory C) ((LKFlat C).obj P)
      ((LKFlat C).obj R)) ℤ := by
  refine commShift_of_whiskerLeft_L _
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (tensorLeftLift P) ((curriedTensor (DerivedCategory C)).flip.obj
        ((LKFlat C).obj R)) ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((curriedTensor (CochainComplex C ℤ)).obj P.obj) (tensorRightLift R) ≫
      (Functor.associator _ _ _).inv)
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (tensorRightLift R) ((curriedTensor (DerivedCategory C)).obj
        ((LKFlat C).obj P)) ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((curriedTensor (CochainComplex C ℤ)).flip.obj R.obj) (tensorLeftLift P) ≫
      (Functor.associator _ _ _).inv)
    (Functor.whiskerRight (associatorNatTrans₂ (CochainComplex C ℤ) P.obj R.obj) (L C)) ?_
  ext Z
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, associatorNatTrans₂_app,
    tensorLeftLift_app, tensorRightLift_app, comp_id, id_comp, curriedTensor_obj_map,
    curriedTensor_map_app, Functor.flip_obj_map, Functor.flip_obj_obj, assoc]
  exact (μ_associativity P.obj Z R.obj).symm

end TensorCommShift₂

open TensorCommShift₂

instance (Y Z : DerivedCategory C) :
    NatTrans.CommShift (associatorNatTrans₁ (DerivedCategory C) Y Z) ℤ := by
  have := Localization.essSurj (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
  have := commShift_associatorNatTrans₁_kFlat ((LKFlat C).objPreimage Y)
    ((LKFlat C).objPreimage Z)
  exact commShift_associatorNatTrans₁_of_iso ((LKFlat C).objObjPreimageIso Y)
    ((LKFlat C).objObjPreimageIso Z)

instance (X Z : DerivedCategory C) :
    NatTrans.CommShift (associatorNatTrans₂ (DerivedCategory C) X Z) ℤ := by
  have := Localization.essSurj (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
  have := commShift_associatorNatTrans₂_kFlat ((LKFlat C).objPreimage X)
    ((LKFlat C).objPreimage Z)
  exact commShift_associatorNatTrans₂_of_iso ((LKFlat C).objObjPreimageIso X)
    ((LKFlat C).objObjPreimageIso Z)

instance (X Y : DerivedCategory C) :
    NatTrans.CommShift (associatorNatTrans₃ (DerivedCategory C) X Y) ℤ := by
  have := Localization.essSurj (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
  have := commShift_associatorNatTrans₃_kFlat ((LKFlat C).objPreimage X)
    ((LKFlat C).objPreimage Y)
  exact commShift_associatorNatTrans₃_of_iso ((LKFlat C).objObjPreimageIso X)
    ((LKFlat C).objObjPreimageIso Y)

variable {C}

lemma shiftTensorShiftIso_assoc_aux (K L M : DerivedCategory C) (b c : ℤ) :
    (((curriedTensor (DerivedCategory C)).obj K).commShiftIso b).hom.app L ▷ M⟦c⟧ ≫
      (((curriedTensor (DerivedCategory C)).flip.obj (M⟦c⟧)).commShiftIso b).hom.app (K ⊗ L) ≫
      ((((curriedTensor (DerivedCategory C)).obj (K ⊗ L)).commShiftIso c).hom.app M ≫
        (α_ K L M).hom⟦c⟧')⟦b⟧' =
    (α_ K (L⟦b⟧) (M⟦c⟧)).hom ≫ K ◁ (shiftTensorShiftIso C L M b c).hom ≫
      (((curriedTensor (DerivedCategory C)).obj K).commShiftIso (b + c)).hom.app (L ⊗ M) ≫
      (shiftFunctorAdd' (DerivedCategory C) c b (b + c) (add_comm c b)).hom.app (K ⊗ (L ⊗ M)) := by
  exact commShiftIso_assoc_aux K L M b c

omit [IsGrothendieckAbelian C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))] in
/-- A coherence of the isomorphisms `X⟦a⟧⟦b⟧ ≅ X⟦a + b⟧`, in the form needed for
`DerivedCategory.shiftTensorShiftIso_assoc`. -/
lemma shiftFunctorAdd'_assoc_aux (W : DerivedCategory C) (a b c : ℤ) :
    ((shiftFunctorAdd' (DerivedCategory C) c b (b + c) (add_comm c b)).hom.app W)⟦a⟧' ≫
      (shiftFunctorAdd' (DerivedCategory C) b a (a + b) (add_comm b a)).inv.app (W⟦c⟧) ≫
      (shiftFunctorAdd' (DerivedCategory C) c (a + b) (a + b + c)
        (add_comm c (a + b))).inv.app W =
    (shiftFunctorAdd' (DerivedCategory C) (b + c) a (a + (b + c))
      (add_comm (b + c) a)).inv.app W ≫ eqToHom (by rw [add_assoc]) := by
  have h := shiftFunctorAdd'_assoc_inv_app (C := DerivedCategory C) c b a (b + c) (a + b)
    (a + b + c) (add_comm c b) (add_comm b a) (by omega) W
  rw [← h, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, id_comp]
  have e : ∀ (n n' : ℤ) (hn : b + c + a = n) (hn' : b + c + a = n') (h : n = n'),
      (shiftFunctorAdd' (DerivedCategory C) (b + c) a n hn).inv.app W =
        (shiftFunctorAdd' (DerivedCategory C) (b + c) a n' hn').inv.app W ≫
          eqToHom (by rw [h]) := by
    rintro n n' hn hn' rfl
    simp
  exact e _ _ _ _ (by omega)

lemma shiftTensorShiftIso_assoc (K L M : DerivedCategory C) (a b c : ℤ) :
    (shiftTensorShiftIso C K L a b).hom ▷ M⟦c⟧ ≫
      (shiftTensorShiftIso C (K ⊗ L) M (a + b) c).hom ≫ (α_ K L M).hom⟦a + b + c⟧' =
    (α_ (K⟦a⟧) (L⟦b⟧) (M⟦c⟧)).hom ≫ K⟦a⟧ ◁ (shiftTensorShiftIso C L M b c).hom ≫
      (shiftTensorShiftIso C K (L ⊗ M) a (b + c)).hom ≫ eqToHom (by rw [add_assoc]) := by
  have h₁ := NatTrans.shift_app_comm (associatorNatTrans₁ (DerivedCategory C) (L⟦b⟧) (M⟦c⟧)) a K
  simp only [Functor.commShiftIso_comp_hom_app, associatorNatTrans₁_app, Functor.comp_obj,
    Functor.flip_obj_map, curriedTensor_map_app, Functor.flip_obj_obj, curriedTensor_obj_obj,
    assoc] at h₁
  have hS := NatTrans.shift_app_comm ((curriedTensor (DerivedCategory C)).flip.map
    (shiftTensorShiftIso C L M b c).hom) a K
  simp only [Functor.flip_map_app, curriedTensor_obj_map] at hS
  have hA := congr_arg (fun f ↦ f⟦a⟧') (shiftTensorShiftIso_assoc_aux K L M b c)
  simp only [Functor.map_comp] at hA
  have hR := Functor.commShiftIso_add' ((curriedTensor (DerivedCategory C)).flip.obj (M⟦c⟧))
    (show b + a = a + b from add_comm b a)
  have hR' := congr_arg (fun e ↦ e.hom.app (K ⊗ L)) hR
  simp only [Functor.CommShift.isoAdd'_hom_app, Functor.flip_obj_map, curriedTensor_map_app]
    at hR'
  have hc : (shiftFunctorAdd' (DerivedCategory C) b a (a + b) (add_comm b a)).inv.app
      (((curriedTensor (DerivedCategory C)).obj K).obj L) ▷ M⟦c⟧ ≫
      (shiftFunctorAdd' (DerivedCategory C) b a (a + b) (add_comm b a)).hom.app (K ⊗ L) ▷ M⟦c⟧ =
      𝟙 _ := by
    rw [← comp_whiskerRight]
    erw [Iso.inv_hom_id_app]
    rw [id_whiskerRight]
  have hN := ((curriedTensor (DerivedCategory C)).flip.obj (M⟦c⟧)).commShiftIso_hom_naturality
    ((((curriedTensor (DerivedCategory C)).obj K).commShiftIso b).hom.app L) a
  simp only [Functor.flip_obj_map, curriedTensor_map_app] at hN
  have hα := (shiftFunctorAdd' (DerivedCategory C) c (a + b) (a + b + c)
    (add_comm c (a + b))).inv.naturality (α_ K L M).hom
  have htail : (shiftFunctorAdd' (DerivedCategory C) b a (a + b) (add_comm b a)).inv.app
        ((K ⊗ L) ⊗ M⟦c⟧) ≫
      ((((curriedTensor (DerivedCategory C)).obj (K ⊗ L)).commShiftIso c).hom.app M)⟦a + b⟧' ≫
      ((α_ K L M).hom⟦c⟧')⟦a + b⟧' =
      (((((curriedTensor (DerivedCategory C)).obj (K ⊗ L)).commShiftIso c).hom.app M)⟦b⟧')⟦a⟧' ≫
      (((α_ K L M).hom⟦c⟧')⟦b⟧')⟦a⟧' ≫
      (shiftFunctorAdd' (DerivedCategory C) b a (a + b) (add_comm b a)).inv.app
        ((K ⊗ (L ⊗ M))⟦c⟧) := by
    have := (shiftFunctorAdd' (DerivedCategory C) b a (a + b) (add_comm b a)).inv.naturality
      ((((curriedTensor (DerivedCategory C)).obj (K ⊗ L)).commShiftIso c).hom.app M ≫
        (α_ K L M).hom⟦c⟧')
    simp only [Functor.comp_map, Functor.map_comp, assoc] at this
    exact this.symm
  have hassoc := shiftFunctorAdd'_assoc_aux (K ⊗ (L ⊗ M)) a b c
  simp only [shiftTensorShiftIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    comp_whiskerRight, assoc] at hS hA ⊢
  rw [hR']
  simp only [assoc]
  rw [reassoc_of% hc]
  erw [reassoc_of% hN]
  erw [← hα]
  erw [reassoc_of% htail]
  erw [reassoc_of% hA]
  erw [reassoc_of% h₁, reassoc_of% hS, hassoc]
  rfl

end DerivedCategory
