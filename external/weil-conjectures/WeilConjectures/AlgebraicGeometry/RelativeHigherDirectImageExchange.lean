/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Degreewise relative exchange with coefficient maps

Source: Stacks Project, Tags 0EYM and 07A7. -/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Degree-q commutative-square exchange followed by the coefficient map.

Source: Stacks Project, Tag 0EYM, first proof paragraph; Tag 07A7, remark-base-change
(blueprint: def-kun-relative-higher-image-exchange).
The first factor identifies inverse image of cohomology with cohomology of inverse
image. The second takes cohomology of the derived mate `derivedBaseChangeMapPlus` and
of the specified coefficient map, using the exact pullback comparison with degree zero.
No cartesian or torsion hypothesis enters this construction. -/
noncomputable def relativeHigherDirectImageExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} g').obj F ⟶ F') (q : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ⟶
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F')) :=
  ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.app
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F) ≫
        (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
          (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlusSingleFunctor
            0).hom.app F ≫
            (DerivedCategory.Plus.singleFunctor
              (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).map φ))

end AlgebraicGeometry.Etale
