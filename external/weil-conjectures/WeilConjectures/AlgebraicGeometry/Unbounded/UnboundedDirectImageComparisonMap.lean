/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation

/-! # Naturality of the canonical unbounded direct-image mate

Source: blueprint `sk-prop-pe-unbounded-classical-direct-image.md`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Naturality of the canonical unbounded mate.
Source: naturality of adjunction transposition; blueprint direct-image proof, Step 10
(blueprint: lem-sfb-unbounded-direct-image-comparison). -/
@[reassoc]
theorem unboundedDirectImageComparisonMap_naturality
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (f : K ⟶ L) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map f) ≫
      unboundedDirectImageComparisonMap A g L =
    unboundedDirectImageComparisonMap A g K ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map f) := by
  let adj := (ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction
  unfold unboundedDirectImageComparisonMap
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  apply congrArg (adj.homEquiv _ _)
  rw [Category.assoc, ← Functor.map_comp]
  have hε := (Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.counit.naturality f
  simp only [Functor.comp_map, Functor.id_map] at hε
  rw [← hε]
  rw [Functor.map_comp, ← Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z ↦ z ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.counit.app L))
      ((unboundedDirectImagePullbackIso A g).hom.naturality
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map f))

end AlgebraicGeometry.ProEtale
