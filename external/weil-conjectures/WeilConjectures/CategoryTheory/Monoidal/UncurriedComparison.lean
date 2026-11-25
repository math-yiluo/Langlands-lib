/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Uncurried comonoidal comparisons

* `CategoryTheory.Functor.prodCompIso`: the identification `F × F ⋙ G × G ≅ (F ⋙ G) × (F ⋙ G)`.
* `CategoryTheory.Functor.OplaxMonoidal.δUncurried`: the comonoidal structure
  `G (X ⊗ Y) ⟶ G X ⊗ G Y` of an oplax monoidal functor `G`, as a natural transformation of
  functors on `C × C`.
* `HomologicalComplex.mapBifunctorComparisonUncurried`: the comparison
  `G (K₁ ⊗_F K₂) ⟶ G K₁ ⊗_{F'} G K₂` of total complexes induced by a natural transformation
  `G (F X₁ X₂) ⟶ F' (G X₁) (G X₂)`, as a natural transformation of functors on pairs of
  complexes.

Stating compatibilities with these natural transformations, instead of componentwise, keeps the
objects in the form of composite functors applied to a pair.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Functor

/-- The functors `F × F ⋙ G × G` and `(F ⋙ G) × (F ⋙ G)` agree. -/
@[simps!]
def prodCompIso {A B C : Type*} [Category* A] [Category* B] [Category* C] (F : A ⥤ B) (G : B ⥤ C) :
    F.prod F ⋙ G.prod G ≅ (F ⋙ G).prod (F ⋙ G) :=
  Iso.refl _

end CategoryTheory.Functor

namespace CategoryTheory.Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (G : C ⥤ D) [G.OplaxMonoidal]

/-- The comonoidal structure `G (X ⊗ Y) ⟶ G X ⊗ G Y`, as a natural transformation of functors
on `C × C`. -/
@[simps]
def δUncurried :
    Functor.uncurry.obj (curriedTensor C) ⋙ G ⟶ G.prod G ⋙ Functor.uncurry.obj (curriedTensor D)
    where
  app X := δ G X.1 X.2
  naturality _ _ f := by
    simp only [Functor.comp_obj, Functor.uncurry_obj_obj, curriedTensor_obj_obj,
      Functor.comp_map, Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
      Functor.prod_obj, Functor.prod_map, ← tensorHom_def, δ_natural]

end CategoryTheory.Functor.OplaxMonoidal

namespace HomologicalComplex

variable {C₁ C₂ D C₁' C₂' D' : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* C₁'] [Category* C₂'] [Category* D']
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  [HasZeroMorphisms C₁'] [HasZeroMorphisms C₂'] [Preadditive D']
  {F : C₁ ⥤ C₂ ⥤ D} [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  {F' : C₁' ⥤ C₂' ⥤ D'} [F'.PreservesZeroMorphisms]
  [∀ X₁, (F'.obj X₁).PreservesZeroMorphisms]
  {G₁ : C₁ ⥤ C₁'} {G₂ : C₂ ⥤ C₂'} {G : D ⥤ D'}
  [G₁.PreservesZeroMorphisms] [G₂.PreservesZeroMorphisms] [G.Additive]
  (τ : (Functor.postcompose₂.obj G).obj F ⟶ (((Functor.whiskeringLeft₂ D').obj G₁).obj G₂).obj F')
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c : ComplexShape J)
  [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ j, Limits.PreservesColimitsOfShape (Discrete (ComplexShape.π c₁ c₂ c ⁻¹' {j})) G]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
    HasMapBifunctor K₁ K₂ F c]
  [∀ (K₁ : HomologicalComplex C₁' c₁) (K₂ : HomologicalComplex C₂' c₂),
    HasMapBifunctor K₁ K₂ F' c]

include τ in
/-- The comparison `G (K₁ ⊗_F K₂) ⟶ G K₁ ⊗_{F'} G K₂` of total complexes
(`HomologicalComplex.mapBifunctorComparison`), as a natural transformation of functors on pairs
of complexes. -/
@[simps]
noncomputable def mapBifunctorComparisonUncurried :
    Functor.uncurry.obj (F.map₂HomologicalComplex c₁ c₂ c) ⋙ G.mapHomologicalComplex c ⟶
      (G₁.mapHomologicalComplex c₁).prod (G₂.mapHomologicalComplex c₂) ⋙
        Functor.uncurry.obj (F'.map₂HomologicalComplex c₁ c₂ c) where
  app K := mapBifunctorComparison τ c K.1 K.2
  naturality K L f := by
    have := (Functor.uncurry.map
      (mapBifunctorComparisonNatTrans (c₁ := c₁) (c₂ := c₂) τ c)).naturality f
    simpa [Functor.map_comp] using this

end HomologicalComplex
