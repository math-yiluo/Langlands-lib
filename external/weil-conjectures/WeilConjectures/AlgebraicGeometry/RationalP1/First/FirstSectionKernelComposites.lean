/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
/-! # Native composites for the first section calculation -/
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
attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- Express a diagram functional in the fixed native first direct image. -/
@[irreducible]
def firstNativeFunctional
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (t : d.R₁.R.obj N ⟶ unit Λ (ProjectiveLine Y)) :
    (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N ⟶
      unit Λ (ProjectiveLine Y) := by
  unfold moduleObjectDerivedPushforward firstProjection
  exact (eqToIso d.p₁_canonical).inv.app N ≫ t

-- Keep the native functor sources fixed while constructing the prefix.
/-- The supported-kernel insertion, with its source and target fixed before direct image.
This is the literal section paste,
followed by the second direct image of the tensor comparison and the supported kernel arrow. -/
@[irreducible]
def firstKernelInsertion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N) :
    M ⟶ (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N) :=
  (pushSectionIso Λ Y).hom.app M ≫
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
      ((diagonalTensorIso Λ Y M).hom ≫
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ◁
          ((supportedUnitIso Λ Y).hom ≫ α)))

-- The terminal functional has the native path objects as its declared endpoints.
/-- Change direct-image paths and evaluate a first-projection functional.
The arrows are the conjugate path
comparison, the inverse projection, identity tensor the given native functional,
identity tensor singleUnitIso, and the right unitor, in that order. -/
@[irreducible]
def firstTerminalFunctional
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (t : d.R₁.R.obj N ⟶ unit Λ (ProjectiveLine Y))
    (hp : IsIso (projectionMap Λ (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N)) ⟶
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M :=
  (firstPathComparison Λ Y).hom.app
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N) ≫
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      (@inv _ _ _ _ (projectionMap Λ (firstProjection Y) M N) hp ≫
        (M ◁ firstNativeFunctional Λ Y L d N t) ≫
        (M ◁ (singleUnitIso Λ (ProjectiveLine Y)).hom) ≫ (ρ_ M).hom)

end AlgebraicGeometry.ProEtale.RationalP1
