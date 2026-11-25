/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegrationComposition.IntegrationTransposeCompositionData
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

set_option linter.privateModule false

/-! # Composition of ordered compact-support integrations
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u u'

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

open Lean Elab Tactic Meta

private theorem swap_naturality
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) (L : D ⥤ C)
    (π : ∀ M K, F.obj M ⊗ K ⟶ F.obj (M ⊗ L.obj K))
    (hn : ∀ {M M'} (v : M ⟶ M') K,
      F.map v ▷ K ≫ π M' K = π M K ≫ F.map (v ▷ L.obj K))
    {M M' : C} (v : M ⟶ M') (K : D) :
    K ◁ F.map v ≫ (β_ K (F.obj M')).hom ≫ π M' K ≫
        F.map (β_ (L.obj K) M').inv =
      ((β_ K (F.obj M)).hom ≫ π M K ≫ F.map (β_ (L.obj K) M).inv) ≫
        F.map (L.obj K ◁ v) := by
  rw [BraidedCategory.braiding_naturality_right_assoc, reassoc_of% hn]
  simp only [Category.assoc, ← F.map_comp]
  rw [BraidedCategory.braiding_inv_naturality_left]

private theorem projection_naturality_general
    (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type (u + 1)} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology B)} (v : M ⟶ M')
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((derivedTensor B Y).obj K).map
        ((rightDerivedLowerShriek B f).map v) ≫
      (((derivedTensorSymmetry B Y).hom.app K).app
        ((rightDerivedLowerShriek B f).obj M') ≫
      ((projectionMap B f).app M').app K ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensor B X).obj M').map
          ((leftDerivedUpperStarIsoMapDerivedCategory B f).hom.app K)) ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensorSymmetry B X).inv.app
          ((upperStar B f).mapDerivedCategory.obj K)).app M')) =
    (((derivedTensorSymmetry B Y).hom.app K).app
        ((rightDerivedLowerShriek B f).obj M) ≫
      ((projectionMap B f).app M).app K ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensor B X).obj M).map
          ((leftDerivedUpperStarIsoMapDerivedCategory B f).hom.app K)) ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensorSymmetry B X).inv.app
          ((upperStar B f).mapDerivedCategory.obj K)).app M)) ≫
      (rightDerivedLowerShriek B f).map
        (((derivedTensor B X).obj
          ((upperStar B f).mapDerivedCategory.obj K)).map v) := by
  let F := rightDerivedLowerShriek B f
  let L := (upperStar B f).leftDerivedFunctor
  let D := (upperStar B f).mapDerivedCategory
  let T := derivedTensor B Y
  let U := derivedTensor B X
  let e := leftDerivedUpperStarIsoMapDerivedCategory B f
  let s := derivedTensorSymmetry B X
  have hY := ((derivedTensorSymmetry B Y).hom.app K).naturality
    (F.map v)
  have hP := congr_app ((projectionMap B f).naturality v) K
  change (T.obj K).map (F.map v) ≫ _ = _ ≫ (T.map (F.map v)).app K at hY
  change (T.map (F.map v)).app K ≫ _ = _ ≫ F.map ((U.map v).app (L.obj K)) at hP
  have he : (U.map v).app (L.obj K) ≫ (U.obj M').map (e.hom.app K) ≫
      (s.inv.app (D.obj K)).app M' =
    (U.obj M).map (e.hom.app K) ≫ (s.inv.app (D.obj K)).app M ≫
      (U.obj (D.obj K)).map v := by
    have hn := (U.map v).naturality (e.hom.app K)
    rw [← reassoc_of% hn]
    exact congrArg ((U.obj M).map (e.hom.app K) ≫ ·)
      ((s.inv.app (D.obj K)).naturality v)
  rw [reassoc_of% hY, reassoc_of% hP]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ ((derivedTensorSymmetry B Y).hom.app K).app (F.obj M) ≫
      ((projectionMap B f).app M).app K ≫ F.map z) he

namespace IntegrationComposition

variable {A : Type (u + 1)} [CommRing A] {X Y Z : Scheme.{u}}

private theorem projection_eq (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    compactSupportProjectionMap A f M K =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
        ((projectionMap (ModuleCat.{u + 1} A) f).app M).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
            ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).app M) := by
  dsimp only [compactSupportProjectionMap, compactSupportProjectionMapOfCompactification,
      projectionMap, rightDerivedLowerShriek]

private theorem projection_naturality (f : X ⟶ Y) [HasCompactification f]
    {M M' : DerivedCategoryModule A X} (v : M ⟶ M') (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map v) ≫
      compactSupportProjectionMap A f M' K =
    compactSupportProjectionMap A f M K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).map v) := by
  rw [projection_eq, projection_eq]
  exact projection_naturality_general (ModuleCat.{u + 1} A) f v K

private instance projection_isIso [Finite A] (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    IsIso (compactSupportProjectionMap A f M K) := by
  have := isIso_projectionMap_of_finite A f
  rw [projection_eq]
  infer_instance

end IntegrationComposition

end AlgebraicGeometry.Etale
