/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric

/-!
# The derived category of a symmetric monoidal category is symmetric

If `C` is a symmetric monoidal category, the Koszul braiding of cochain complexes
(`CochainComplex.Monoidal.braidedCategory`) is symmetric
(`CochainComplex.Monoidal.braiding_hom_braiding_hom`). Hence so are the braiding of the homotopy
category (`HomotopyCategory.braidedCategory`) and the braiding descended to the derived monoidal
category (`CategoryTheory.DerivedMonoidal.braidedCategory'`), in particular the braiding
`DerivedCategory.braidedCategory' C` of the derived tensor product on `DerivedCategory C`. This
file packages these facts as `SymmetricCategory` structures.

## Main definitions

- `CochainComplex.Monoidal.symmetricCategory`, `HomotopyCategory.symmetricCategory`,
  `CategoryTheory.DerivedMonoidal.symmetricCategory`, `DerivedCategory.symmetricCategory'`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex.Monoidal

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C] [SymmetricCategory C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- The Koszul braiding makes cochain complexes over a symmetric category a symmetric monoidal
category. -/
@[instance_reducible]
noncomputable def symmetricCategory : SymmetricCategory (CochainComplex C ℤ) where
  toBraidedCategory := braidedCategory
  symmetry := braiding_hom_braiding_hom (fun _ _ ↦ SymmetricCategory.symmetry _ _)

end CochainComplex.Monoidal

namespace HomotopyCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C] [SymmetricCategory C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The braiding of the homotopy category of cochain complexes over a symmetric category is
symmetric. -/
@[instance_reducible]
noncomputable def symmetricCategory : SymmetricCategory (HomotopyCategory C (.up ℤ)) where
  toBraidedCategory := braidedCategory
  symmetry := braiding_hom_braiding_hom (fun _ _ ↦ SymmetricCategory.symmetry _ _)

end HomotopyCategory

namespace CategoryTheory.DerivedMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [SymmetricCategory C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]
  [L.HasDerivedMonoidalCategory W] [W.RespectsIso] [W.HasTwoOutOfThreeProperty]
  [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]

/-- Over a symmetric category, the derived monoidal category is symmetric. -/
@[instance_reducible]
noncomputable def symmetricCategory : SymmetricCategory (DerivedMonoidal L W) where
  toBraidedCategory := braidedCategory' L W
  symmetry := braiding_hom_braiding_hom L W (fun _ _ ↦ SymmetricCategory.symmetry _ _)

end CategoryTheory.DerivedMonoidal

namespace DerivedCategory

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local instance hasColimitsOfSize_symmetricCategory_derivedCategorySymmetric
    : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]

/-- The derived category of a symmetric monoidal closed Grothendieck abelian category with
functorial flat resolutions is symmetric for the Koszul braiding
`DerivedCategory.braidedCategory' C`. -/
@[instance_reducible]
noncomputable def symmetricCategory' : SymmetricCategory (DerivedCategory C) where
  toBraidedCategory := braidedCategory' C
  symmetry := braiding_hom_braiding_hom C (fun _ _ ↦ SymmetricCategory.symmetry _ _)

end DerivedCategory
