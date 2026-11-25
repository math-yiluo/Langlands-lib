/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveCanonicalSectionProjection
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSupportedSourceNormalization

/-! # Projection coherence on the supported diagonal source

## References

* Stacks Tags 0B56 and 0DV0
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist firstProjection secondProjection square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] projectionMap singleUnitIso secondLineComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- The statement compares the fixed derived pullback and tensor interfaces.
/-- Section/projection coherence on the supported coefficient source, before any class map. -/
theorem supported_section_projection
    (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (ρ_ M).inv ≫
      (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
        (secondDiagramPushIso Λ Y L d).hom.app
          ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (source Λ Y)))) ≫
      projectionMap Λ (secondProjection Y) M
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        ((((moduleObjectDerivedPullback Λ (secondProjection Y)).obj M) ◁
          (supportedUnitIso Λ Y).inv) ≫
          sectionTensorMap Λ (diagonalImmersion Y) (secondProjection Y)
            (pullSectionIso Λ Y (secondProjection Y)
              (by unfold secondProjection; exact pullback.diagonal_snd _))
            (unit Λ (ProjectiveLine Y)) (singleUnitIso Λ (ProjectiveLine Y)) M) =
      (pushSectionIso Λ Y).hom.app M := by
  rw [supported_source_normalization Λ Y L d M]
  exact canonical_section_projection Λ Y M

end AlgebraicGeometry.ProEtale.RationalP1
