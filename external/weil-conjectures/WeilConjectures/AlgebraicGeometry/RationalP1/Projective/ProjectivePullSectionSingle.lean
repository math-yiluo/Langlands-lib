/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

/--
The single-complex component of the derived pullback section is the ordinary
section map conjugated by the two left-derived single comparisons.
-/
theorem projective_pull_section_single (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (M : Modules Λ (ProjectiveLine Y)) :
    (pullSectionIso Λ Y f h).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M) =
      (CondensedRing.upperStar Λ (diagonalImmersion Y)).leftDerivedFunctor.map
        ((CategoryTheory.Functor.singleFunctorCompLeftDerivedFunctorIso
          (CondensedRing.upperStar Λ f)).hom.app M) ≫
      (CategoryTheory.Functor.singleFunctorCompLeftDerivedFunctorIso
        (CondensedRing.upperStar Λ (diagonalImmersion Y))).hom.app
          ((CondensedRing.upperStar Λ f).obj M) ≫
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
        (((CondensedRing.upperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
          CondensedRing.upperStarCongr Λ h ≪≫
          CondensedRing.upperStarId Λ (ProjectiveLine Y)).hom.app M) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
