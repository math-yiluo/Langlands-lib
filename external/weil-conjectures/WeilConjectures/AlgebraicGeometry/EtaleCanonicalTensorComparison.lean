/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Explicit type of the canonical tensor comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
@[irreducible]
def canonicalPullbackTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(upperStar B f).PreservesFlat] :
    (Functor.postcompose₂.obj (upperStar B f).leftDerivedFunctor).obj
        (derivedTensor B Y) ⟶
      (((Functor.whiskeringLeft₂ _).obj (upperStar B f).leftDerivedFunctor).obj
        (upperStar B f).leftDerivedFunctor).obj
          (derivedTensor B X) := by
  let d := leftDerivedUpperStarTensorComparison B f
  dsimp only [leftDerivedUpperStarDerivedTensor, derivedTensorLeftDerivedUpperStar] at d
  exact d

theorem canonicalPullbackTensorComparison_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(upperStar B f).PreservesFlat] :
    canonicalPullbackTensorComparison B f = leftDerivedUpperStarTensorComparison B f := by
  unfold canonicalPullbackTensorComparison
  rfl
/-- Componentwise equality with the canonical source comparison. -/
theorem canonicalPullbackTensorComparison_app_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(upperStar B f).PreservesFlat]
    (M N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((canonicalPullbackTensorComparison B f).app M).app N =
      ((leftDerivedUpperStarTensorComparison B f).app M).app N := by
  rw [canonicalPullbackTensorComparison_eq]

instance isIso_canonicalPullbackTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(upperStar B f).PreservesFlat]
    (M N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    IsIso (((canonicalPullbackTensorComparison B f).app M).app N) := by
  rw [canonicalPullbackTensorComparison_eq]
  infer_instance
theorem canonicalPullbackTensorComparison_app_eq_delta {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(upperStar B f).PreservesFlat]
    (M N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    letI := leftDerivedUpperStarOplaxMonoidal B f
    ((canonicalPullbackTensorComparison B f).app M).app N =
      Functor.OplaxMonoidal.δ (upperStar B f).leftDerivedFunctor M N := by
  rw [canonicalPullbackTensorComparison_eq]
  rfl
/-- The tensor-right pullback isomorphism uses the canonical tensor comparison. -/
theorem canonicalTensorRightPullback_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(upperStar B f).PreservesFlat]
    (K L : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (derivedTensorRightCompLeftDerivedUpperStarIso B f L).hom.app K =
      ((canonicalPullbackTensorComparison B f).app K).app L := by
  rw [canonicalPullbackTensorComparison_eq]
  rfl
end AlgebraicGeometry.Etale
