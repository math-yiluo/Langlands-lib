/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Normalization of the two ordered projection presentations -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 21000] sheafBraidedCategory
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory
attribute [local instance] DerivedCategory.symmetricCategory'
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
/-- The same ordered projection, written with the cached canonical symmetry. -/
theorem orderedProjection_eq_symmetry {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (((derivedUpperStarLowerStarAdjunction B f).rightAdjointProjectionMap
      (T_C := (derivedTensor B X).flip) (T_D := (derivedTensor B Y).flip)
      ((flipFunctor _ _ _).map (canonicalPullbackTensorComparison B f))).app E).app K =
      ((derivedTensorSymmetry B Y).hom.app K).app
          ((lowerStar B f).rightDerivedFunctor.obj E) ≫
        ((rightDerivedLowerStarProjectionMap B f).app E).app K ≫
        (lowerStar B f).rightDerivedFunctor.map
          (((derivedTensorSymmetry B X).hom.app E).app
            ((upperStar B f).leftDerivedFunctor.obj K)) := by
  simp only [derivedTensorSymmetry, DerivedCategory.canonicalTensorSymmetry,
    BraidedCategory.curriedBraidingNatIso_hom_app_app]
  convert orderedProjection_eq B f E K using 3 <;> rfl

end AlgebraicGeometry.Etale
