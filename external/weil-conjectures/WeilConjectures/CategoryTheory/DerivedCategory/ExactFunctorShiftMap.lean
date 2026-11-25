/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Exact functors and the connecting morphisms of homology sequences

Let `F : C ⥤ D` be an exact functor between abelian categories. The commutation isomorphisms
`H^n(-) ⋙ F ≅ F.mapDerivedCategory ⋙ H^n(-)` (`Functor.mapDerivedCategoryHomologyFunctorIso`)
are compatible with the morphisms `(homologyFunctor C 0).shiftMap f a a'` induced in homology by
morphisms `f : X ⟶ Y⟦n⟧` of the derived category, among which the connecting morphisms of the
long exact homology sequences of distinguished triangles
(`CategoryTheory.Functor.map_shiftMap_homologyFunctor_comp_mapDerivedCategoryHomologyFunctorIso`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

open DerivedCategory in
/-- An exact functor `F` commutes with the morphisms induced in homology by morphisms
`f : X ⟶ Y⟦n⟧` of the derived category: through the isomorphisms
`Functor.mapDerivedCategoryHomologyFunctorIso`, `F` applied to `Hᵃ(X) ⟶ Hᵃ'(Y)` is the morphism
induced by `F.mapDerivedCategory.map f`, followed by the commutation of `F.mapDerivedCategory`
with the shift. -/
@[reassoc]
lemma map_shiftMap_homologyFunctor_comp_mapDerivedCategoryHomologyFunctorIso (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] {X Y : DerivedCategory C}
    {n : ℤ} (f : X ⟶ Y⟦n⟧) (a a' : ℤ) (h : n + a = a') :
    F.map ((homologyFunctor C 0).shiftMap f a a' h) ≫
        (F.mapDerivedCategoryHomologyFunctorIso a').hom.app Y =
      (F.mapDerivedCategoryHomologyFunctorIso a).hom.app X ≫
        (homologyFunctor D 0).shiftMap
          (F.mapDerivedCategory.map f ≫ (F.mapDerivedCategory.commShiftIso n).hom.app Y)
          a a' h := by
  have hn := (F.mapDerivedCategoryHomologyFunctorIso a).hom.naturality f
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [Functor.shiftMap, Functor.shiftMap, F.map_comp, Category.assoc,
    mapDerivedCategoryHomologyFunctorIso_hom_app_shiftIso, Functor.map_comp, Category.assoc]
  exact (Category.assoc _ _ _).symm.trans ((hn =≫ _).trans (Category.assoc _ _ _))

end CategoryTheory.Functor
