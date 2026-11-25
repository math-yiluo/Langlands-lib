/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison


public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison

/-! # The fixed scalar-forgetting map on raw derived Hom

Source: Stacks Project, Tag 03FD, and the free represented sections adjunction.
(blueprint: def-sbc-raw-module-abelian-hom-map).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Forget the derived class and precompose with the map of free represented sheaves.
The coefficient identification is the unique inverse of the inverse-image mate.
Source: Stacks Project, Tag 03FD, and Tags 03D3 and 03D7.
(blueprint: def-sbc-raw-module-abelian-hom-map). -/
noncomputable def rawModuleAbelianHomMap
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (U : S.Etale) (A : Over W) :
    (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op A) ⟶
      (abelianHigherDirectImageRawPresheaf (A.hom ≫ k) q
        (restrictedOverCoefficient
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
          A)).obj (op U) := by
  let V := moduleAbelianForget Λ A.left
  let F := (upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G
  let L := (upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k)).obj ((freeSheaf Λ S).obj U)
  let a := (upperStar AddCommGrpCat.{u + 1} (A.hom ≫ k)).map
      (RawModuleScalarComparison.freeMap Λ S U) ≫
    RawModuleScalarComparison.pullback Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
  let b := (V.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (q : ℤ)).map
      ((V.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ A.hom G)))
  let c := (DerivedCategory.Plus.singleFunctor _ 0).map a ≫
    (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L
  exact AddCommGrpCat.ofHom
    (((Preadditive.leftComp _ c).comp (Preadditive.rightComp _ b)).comp
      (V.mapDerivedCategoryPlus.mapAddHom))

end AlgebraicGeometry.Etale
