/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexSemilinearExtension

/-! # The canonical augmentation after scalar extension

Source: Stacks Project, Tags 03EK and 099D(c).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry

/-- Multiplication `B ⊗ A → B`, defined by the semilinear extension adjunction. -/
def ringComplexScalarUnit {A B : CommRingCat.{u}} (φ : A →+* B) :
    (ringComplexExtension φ).obj (ringComplexUnit A) ⟶ ringComplexUnit B :=
  ringComplexSemilinearLift φ _ _
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := φ.map_mul }

/-- The scalar-extension map on the ring concentrated in degree zero. -/
def ringComplexScalarSingle {A B : CommRingCat.{u}} (φ : A →+* B) :
    ringComplexExtensionComplex φ (ringComplexSingle A) ⟶ ringComplexSingle B :=
  ((HomologicalComplex.singleMapHomologicalComplex (ringComplexExtension φ)
    (.up ℤ) 0).app (ringComplexUnit A)).hom ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map (ringComplexScalarUnit φ)

/-- Apply scalar extension to an augmentation, followed by multiplication on the unit. -/
def ringComplexScalarAugmentation {A B : CommRingCat.{u}} (φ : A →+* B)
    {P : CochainComplex (RingSiteModules A) ℤ} (ε : P ⟶ ringComplexSingle A) :
    ringComplexExtensionComplex φ P ⟶ ringComplexSingle B :=
  ((ringComplexExtension φ).mapHomologicalComplex (.up ℤ)).map ε ≫
    ringComplexScalarSingle φ

/-- The canonical scalar augmentation has the required pure-tensor normalization. -/
theorem ringComplexScalarAugmentation_one_tmul {A B : CommRingCat.{u}} (φ : A →+* B)
    {P : CochainComplex (RingSiteModules A) ℤ} (ε : P ⟶ ringComplexSingle A)
    (x : (P.X 0).val.obj (op ⟨PUnit.unit⟩)) :
    ringComplexAugmentationValue (ringComplexScalarAugmentation φ ε)
      ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
        (ringSiteMap φ) (P.X 0)).presheaf).app (op ⟨PUnit.unit⟩)
          ((1 : B) ⊗ₜ[A, φ] x)) = φ (ringComplexAugmentationValue ε x) := by
  let E := ringComplexExtension φ
  have hs : (ringComplexScalarSingle φ).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit B)).hom =
      E.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)).hom ≫
        ringComplexScalarUnit φ := by
    simp only [ringComplexScalarSingle, HomologicalComplex.comp_f, Iso.app_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    rfl
  change ((E.map (ε.f 0) ≫ (ringComplexScalarSingle φ).f 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit B)).hom).val.app
      (op ⟨PUnit.unit⟩)) _ = _
  rw [hs, ← E.map_comp_assoc]
  change (ringComplexScalarUnit φ).val.app (op ⟨PUnit.unit⟩)
    ((E.map (ε.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)).hom)).val.app
        (op ⟨PUnit.unit⟩) _) = _
  rw [ringComplexExtension_map_one_tmul]
  exact ringComplexSemilinearLift_one_tmul φ _ _ _ _

end AlgebraicGeometry
