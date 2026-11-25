/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralCohomologySitePullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback

/-! # Pullback of the integral pro-etale line-bundle class

Source: blueprint chap-Smooth-purity, classes proof (2).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w₁ w₂ w₃ w₄ t₁ t₂ t₃ t₄

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] Functor.mapDerivedCategory lineBundleEtaleClass lineBundleClass
attribute [local irreducible] mapSingleArrow mapExtensionEndpoints

private theorem pic_map_ofIsInvertible {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    (L : Y.Modules) [Scheme.Modules.IsInvertible L] :
    Scheme.Pic.map f (Scheme.Pic.ofIsInvertible L) =
      Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L) := by
  apply (Scheme.Pic.eq_ofIsInvertible_iff _ _).2
  exact ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Scheme.Modules.pullback f).mapIso (Scheme.Pic.ofIsInvertibleIso L)⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pullback of the line-bundle class before making a constant tower.
Source: blueprint classes proof (2); the already proved Picard cohomology pullback
formula, transported across the canonical site square.
(blueprint: lem-sp-line-bundle-proetale-class-pullback).

Proof: the arbitrary-scheme Picard cohomology naturality theorem identifies the
pulled back class with that of Pic.map f (Pic.ofIsInvertible L). Pulling back the
canonical representative isomorphism identifies this Picard element with
Pic.ofIsInvertible (f*L). Apply integral_cohomology_site_pullback to that class
and the given units map. Its two sides are precisely lineBundleEtaleClass, by
definition. No flatness, nonemptiness or invertibility of a units comparison is used. -/
theorem lineBundle_proEtaleClass_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [Scheme.Modules.IsInvertible L]
    (a : (upperStar AddCommGrpCat.{u + 1} f).obj (Scheme.proEtaleUnitsSheaf Y) ⟶
      Scheme.proEtaleUnitsSheaf X)
    (ha : ∀ (U : Y.ProEtᵒᵖ) (x : (Scheme.proEtaleUnitsSheaf Y).obj.obj U),
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _) a).hom.app
          U x = ULift.up (Additive.ofMul
          (Units.map (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom x.down.toMul))) :
    mapSingleArrow (upperStar AddCommGrpCat.{u + 1} f) 1
        (lineBundleEtaleClass Y (Scheme.Pic.ofIsInvertible L)) ≫
        ((DerivedCategory.singleFunctor (DiagonalAb X) 0).map a)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor (DiagonalAb X) 0).map
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
            (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≫
        lineBundleEtaleClass X
          (Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L)) := by
  have h := integral_cohomology_site_pullback f
    (Scheme.Pic.toCohomologicalPicardGroup Y (Scheme.Pic.ofIsInvertible L)) a ha
  rw [Scheme.gmCohomologyMap_toCohomologicalPicardGroup, pic_map_ofIsInvertible] at h
  simpa only [lineBundleEtaleClass] using h

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
