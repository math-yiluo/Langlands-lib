/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

set_option linter.privateModule false

/-! The canonical projection map is invertible on the third vertex of a distinguished
triangle whenever it is invertible on the first two vertices. -/

@[expose] public section
universe u' u
open CategoryTheory Abelian Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
open DerivedCategory

section

variable [(g)^*[A].PreservesFlat]

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

private lemma comparison_eq :
    leftDerivedUpperStarTensorComparison A g =
      Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
        (leftDerivedUpperStarDerivedTensorCounit A g)
        (Functor.postcompose₂MapWhiskeringLeft₂
          (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh) :=
  rfl

end
end AlgebraicGeometry.Etale
