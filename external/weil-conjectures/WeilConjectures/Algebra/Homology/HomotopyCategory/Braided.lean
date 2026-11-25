/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# The homotopy category of cochain complexes is braided

If `C` is a braided monoidal preadditive category, the Koszul braiding of cochain complexes
(`CochainComplex.Monoidal.braidedCategory`) descends to the homotopy category
`HomotopyCategory C (ComplexShape.up ℤ)`: the braiding of `quotient K ⊗ quotient L` is the image
of the braiding `K ⊗ L ≅ L ⊗ K` (`HomotopyCategory.braidedCategory`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace HomotopyCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

lemma quotient_map_associator_hom (K L M : CochainComplex C ℤ) :
    (quotient C (.up ℤ)).map (α_ K L M).hom =
      (α_ ((quotient C _).obj K) ((quotient C _).obj L) ((quotient C _).obj M)).hom :=
  (MonoidalCategory.associator_hom_app_app_app K L M).symm

lemma quotient_map_associator_inv (K L M : CochainComplex C ℤ) :
    (quotient C (.up ℤ)).map (α_ K L M).inv =
      (α_ ((quotient C _).obj K) ((quotient C _).obj L) ((quotient C _).obj M)).inv := by
  have : (quotient C (.up ℤ)).mapIso (α_ K L M) =
      α_ ((quotient C _).obj K) ((quotient C _).obj L) ((quotient C _).obj M) :=
    Iso.ext (quotient_map_associator_hom K L M)
  exact congrArg Iso.inv this

variable [BraidedCategory C]

/-- The braiding of the homotopy category, induced by the Koszul braiding of cochain
complexes. -/
noncomputable def braiding (K L : HomotopyCategory C (.up ℤ)) : K ⊗ L ≅ L ⊗ K :=
  (quotient C (.up ℤ)).mapIso (β_ K.as L.as)

lemma braiding_quotient (K L : CochainComplex C ℤ) :
    braiding ((quotient C _).obj K) ((quotient C _).obj L) = (quotient C _).mapIso (β_ K L) :=
  rfl


/-- The braided monoidal structure on the homotopy category of cochain complexes. -/
noncomputable instance braidedCategory : BraidedCategory (HomotopyCategory C (.up ℤ)) where
  braiding := braiding
  braiding_naturality_left {X Y} f Z := by
    obtain ⟨X, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨Y, rfl⟩ := Y.quotient_obj_surjective
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    obtain ⟨f, rfl⟩ := (quotient C _).map_surjective f
    have := (quotient C _).congr_map (BraidedCategory.braiding_naturality_left f Z)
    simp only [Functor.map_comp] at this
    exact this
  braiding_naturality_right X {Y Z} g := by
    obtain ⟨X, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨Y, rfl⟩ := Y.quotient_obj_surjective
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    obtain ⟨g, rfl⟩ := (quotient C _).map_surjective g
    have := (quotient C _).congr_map (BraidedCategory.braiding_naturality_right X g)
    simp only [Functor.map_comp] at this
    exact this
  hexagon_forward X Y Z := by
    obtain ⟨X, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨Y, rfl⟩ := Y.quotient_obj_surjective
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    have := (quotient C _).congr_map (BraidedCategory.hexagon_forward X Y Z)
    simp only [Functor.map_comp, quotient_map_associator_hom] at this
    exact this
  hexagon_reverse X Y Z := by
    obtain ⟨X, rfl⟩ := X.quotient_obj_surjective
    obtain ⟨Y, rfl⟩ := Y.quotient_obj_surjective
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    have := (quotient C _).congr_map (BraidedCategory.hexagon_reverse X Y Z)
    simp only [Functor.map_comp, quotient_map_associator_inv] at this
    exact this

end HomotopyCategory
