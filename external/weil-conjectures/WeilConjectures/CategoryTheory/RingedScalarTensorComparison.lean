/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData

/-! # Ordinary scalar extension as tensor with the coefficient module

Source: Stacks Project, Tags 03EK and 03CZ.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
open MonoidalCategory

namespace CategoryTheory.ConstantCompletion

variable {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
  {R S : Sheaf T CommRingCat.{w}}

/-- The coefficient ring, restricted to the original ring. -/
abbrev scalarTensorModule (f : R ⟶ S) : Mod R :=
  (res f).obj (SheafOfModules.unit (siteModuleRings S))

/-- Ordinary tensor cancellation, followed by the scalar ring's left unitor. -/
def scalarTensorModuleIso (f : R ⟶ S) (M : Mod R) :
    (SheafOfModules.monoidalCategory R).tensorObj M (scalarTensorModule f) ≅
      (res f).obj ((change f).obj M) := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  letI := SheafOfModules.monoidalCategory S
  let e := (SheafOfModules.exists_changeOfRings_tensorCancellation_sections
    f).choose
  exact (β_ M (scalarTensorModule f)) ≪≫
    (e (SheafOfModules.unit (siteModuleRings S)) M).symm ≪≫
    (res f).mapIso (λ_ ((change f).obj M))

/-- Naturality of the explicit module contraction.
Source: Stacks Project, Section tensor-product (03EK).
(auxiliary; not a blueprint node). -/
theorem scalarTensorModuleIso_naturality (f : R ⟶ S)
    {M N : Mod R} (a : M ⟶ N) :
    (SheafOfModules.monoidalCategory R).tensorHom a (𝟙 _) ≫
      (scalarTensorModuleIso f N).hom =
    (scalarTensorModuleIso f M).hom ≫ (res f).map ((change f).map a) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalCategory S
  let e := (SheafOfModules.exists_changeOfRings_tensorCancellation_sections
    f).choose
  have he := (SheafOfModules.exists_changeOfRings_tensorCancellation_sections
    f).choose_spec.1 (𝟙 (SheafOfModules.unit (siteModuleRings S))) a
  have hi : (𝟙 (scalarTensorModule f) ⊗ₘ a) ≫
      (e (SheafOfModules.unit (siteModuleRings S)) N).inv =
    (e (SheafOfModules.unit (siteModuleRings S)) M).inv ≫
      (res f).map (𝟙 (SheafOfModules.unit (siteModuleRings S)) ⊗ₘ (change f).map a) := by
    apply (cancel_epi (e (SheafOfModules.unit (siteModuleRings S)) M).hom).mp
    simpa only [e, res, change, Functor.map_id, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun k ↦ k ≫ (e (SheafOfModules.unit (siteModuleRings S)) N).inv) he.symm
  dsimp only [scalarTensorModuleIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc]
  erw [reassoc_of% hi]
  simp only [Category.assoc, ← Functor.map_comp, id_tensorHom]
  erw [leftUnitor_naturality]
  rfl

/-- The canonical ordinary chain comparison, with no K-flatness hypothesis. -/
def scalarTensorComplexIso (f : R ⟶ S) (P : Cx R) :
    ((ringedKoszulTensor R).obj P).obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (scalarTensorModule f)) ≅
      ((res f).mapHomologicalComplex (.up ℤ)).obj
        (((change f).mapHomologicalComplex (.up ℤ)).obj P) := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  letI := Classical.choice (SheafOfModules.tensorClosed R).1
  letI := Classical.choice (SheafOfModules.tensorClosed R).2.1
  let i : (curriedTensor (Mod R)).flip.obj (scalarTensorModule f) ≅ change f ⋙ res f :=
    NatIso.ofComponents (scalarTensorModuleIso f) (fun a ↦
      by
        simpa only [Functor.flip_obj_map, curriedTensor_map_app, Functor.comp_map,
          tensorHom_id] using scalarTensorModuleIso_naturality f a)
  exact CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Mod R))
      (scalarTensorModule f) P ≪≫
    (NatIso.mapHomologicalComplex i (.up ℤ)).app P

end CategoryTheory.ConstantCompletion
