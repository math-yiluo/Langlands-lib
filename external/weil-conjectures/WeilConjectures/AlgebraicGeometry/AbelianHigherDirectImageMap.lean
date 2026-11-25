/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-!
# Transition maps of higher direct images of abelian sheaves

Source: Stacks Project, Lemma 59.51.7, Tag 09Z1, canonical comparison
(blueprint: def-sbc-abelian-higher-direct-image-map).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The canonical map `R^p h_* F → R^p h'_* F'` for `a ≫ h = h'` and
`φ : a⁻¹ F → F'`, on abelian sheaves. It is obtained from the derived adjunction unit,
the pullback composition isomorphism, the derived adjunction counit, and `φ`, followed
by degree-`p` homology. Source: Stacks, Tag 09Z1, comparison morphism
(blueprint: def-sbc-abelian-higher-direct-image-map). -/
noncomputable def abelianHigherDirectImageMap {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F ⟶ F') :
    (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (R+((h)_*[AddCommGrpCat.{u + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
    (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (R+((h')_*[AddCommGrpCat.{u + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F')) :=
  (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h').derivedPlus.unit.app _ ≫
      R+((h')_*[AddCommGrpCat.{u + 1}]).map
        ((eqToIso (congrArg
            (fun t : Y' ⟶ S => ((t)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus)
            w.symm)).hom.app _ ≫
          (upperStarPlusComp AddCommGrpCat.{u + 1} a h).hom.app _ ≫
          D+((a)^*[AddCommGrpCat.{u + 1}]).map
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.counit.app
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
          (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map φ))

end AlgebraicGeometry.Etale
