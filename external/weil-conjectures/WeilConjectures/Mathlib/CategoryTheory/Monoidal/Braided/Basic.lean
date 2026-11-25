/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The right adjoint of a braided functor is lax braided

Let `adj : F ⊣ G` be an adjunction between braided monoidal categories, where `F` is
braided, `G` is lax monoidal, and the adjunction is compatible with the (lax) monoidal
structures (`adj.IsMonoidal`). Then `G` is lax braided: the lax monoidal structure on the
right adjoint automatically preserves the braiding. This is an instance of doctrinal
adjunction; the braided axiom for `G` follows from the one for `F` by transposition
through the adjunction.

## Main definitions

- `CategoryTheory.Adjunction.rightAdjointLaxBraided`: the lax braided structure on the
  right adjoint of a braided functor.
- `CategoryTheory.BraidedCategory.tensorRightEquivalence`: in a braided category, tensoring
  with an object `X` with `X ⊗ Y ≅ 𝟙_ C` is an autoequivalence.

## Main results

- `CategoryTheory.Adjunction.μ_comp_map_braiding`: conversely, the strong monoidal left adjoint
  of a lax braided functor, for a monoidal adjunction, is braided.

- `CategoryTheory.Adjunction.rightAdjointLaxMonoidal_μ_comp_map_braiding`: the lax monoidal
  structure `Adjunction.rightAdjointLaxMonoidal` on the right adjoint of a braided functor is
  compatible with the braidings.
- `CategoryTheory.BraidedCategory.preservesColimitsOfShape_flip_curriedTensor_obj`: in a
  braided category, tensoring on the right with `X` preserves the colimits of shape `J` that
  tensoring on the left with `X` preserves, the two functors being identified by the braiding.
- `CategoryTheory.MonoidalCategory.leftUnitor_inv_whiskerRight_tensorμ_leftUnitor`: the
  middle-four interchange with the unit in the first slot is a braiding.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Braided] [G.LaxMonoidal] [adj.IsMonoidal]

/-- If `adj : F ⊣ G` is an adjunction between braided categories, `F` is braided, `G` is
lax monoidal, and the adjunction is compatible with the monoidal structures, then `G` is
lax braided: transposing the braided axiom for `F` through the adjunction yields the
braided axiom for `G`. -/
@[implicit_reducible]
def rightAdjointLaxBraided : G.LaxBraided where
  braided X Y := by
    apply (adj.homEquiv _ _).symm.injective
    rw [homEquiv_counit, homEquiv_counit, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, counit_naturality,
      map_μ_comp_counit_app_tensor_assoc, map_μ_comp_counit_app_tensor,
      BraidedCategory.braiding_naturality, Functor.map_braiding, Category.assoc,
      Category.assoc, Functor.Monoidal.μ_δ_assoc]

section

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Braided]

/-- The right adjoint of a braided monoidal functor, with its lax monoidal structure
`Adjunction.rightAdjointLaxMonoidal`, is compatible with the braidings: the square
```
  G X ⊗ G Y ──μ──▶ G (X ⊗ Y)
      │                │
   β_(G X, G Y)     G (β_(X, Y))
      ▼                ▼
  G Y ⊗ G X ──μ──▶ G (Y ⊗ X)
```
commutes. -/
lemma rightAdjointLaxMonoidal_μ_comp_map_braiding (X Y : D) :
    letI := adj.rightAdjointLaxMonoidal
    μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X := by
  let := adj.rightAdjointLaxMonoidal
  rw [rightAdjointLaxMonoidal_μ, rightAdjointLaxMonoidal_μ, homEquiv_unit, homEquiv_unit,
    Category.assoc, ← G.map_comp, ← adj.unit_naturality_assoc, ← G.map_comp]
  congr 2
  simp

end

section LeftAdjoint

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Monoidal] [G.LaxBraided]

/-- **The left adjoint of a lax braided functor is braided**, for a monoidal adjunction:
the braided axiom for `F` follows from the one for `G` by transposition. -/
lemma map_braiding_comp_δ (adj : F ⊣ G) [adj.IsMonoidal] (X Y : C) :
    F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  erw [adj.unit_naturality_assoc]
  rw [adj.unit_app_tensor_comp_map_δ,
    adj.unit_app_tensor_comp_map_δ_assoc, Functor.LaxBraided.braided,
    BraidedCategory.braiding_naturality_assoc]

/-- **The left adjoint of a lax braided functor is braided**, stated with the multiplication
`μ` of the strong monoidal left adjoint. -/
lemma μ_comp_map_braiding (adj : F ⊣ G) [adj.IsMonoidal] (X Y : C) :
    μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X := by
  rw [← cancel_mono (δ F Y X), Category.assoc, map_braiding_comp_δ adj, Functor.Monoidal.μ_δ_assoc,
    Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

end LeftAdjoint

end CategoryTheory.Adjunction

namespace CategoryTheory.BraidedCategory

open Limits MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {J : Type*} [Category* J]

/-- In a braided monoidal category, if tensoring on the left with any object preserves
colimits of shape `J`, then so does tensoring on the right, since the braiding identifies
`tensorLeft X` with `tensorRight X`. -/
instance preservesColimitsOfShape_flip_curriedTensor_obj
    [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)] (X : C) :
    PreservesColimitsOfShape J ((curriedTensor C).flip.obj X) :=
  preservesColimitsOfShape_of_natIso (tensorLeftIsoTensorRight X)

/-- **Tensoring with an invertible object is an autoequivalence.** If `X ⊗ Y ≅ 𝟙_ C` in a
braided monoidal category, then `tensorRight X` is an equivalence, with inverse
`tensorRight Y`: both composites are tensoring with `X ⊗ Y ≅ Y ⊗ X ≅ 𝟙_ C`. -/
@[simps! functor inverse]
def tensorRightEquivalence (X Y : C) (e : X ⊗ Y ≅ 𝟙_ C) : C ≌ C :=
  Equivalence.mk (tensorRight X) (tensorRight Y)
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso e.symm ≪≫ tensorRightTensor X Y)
    ((tensorRightTensor Y X).symm ≪≫ (tensoringRight C).mapIso (β_ Y X ≪≫ e) ≪≫
      rightUnitorNatIso C)

end CategoryTheory.BraidedCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]

/-- The middle-four interchange with the unit in the first slot is the braiding of the next two
factors: `λ⁻¹ ▷ _ ≫ tensorμ 𝟙 A B D ≫ λ ▷ _ = α⁻¹ ≫ β_{A,B} ▷ D ≫ α`. -/
@[reassoc]
lemma leftUnitor_inv_whiskerRight_tensorμ_leftUnitor (A B D : C) :
    (λ_ A).inv ▷ (B ⊗ D) ≫ tensorμ (𝟙_ C) A B D ≫ (λ_ B).hom ▷ (A ⊗ D) =
      (α_ A B D).inv ≫ (β_ A B).hom ▷ D ≫ (α_ B A D).hom := by
  simp only [tensorμ]
  monoidal

end CategoryTheory.MonoidalCategory
