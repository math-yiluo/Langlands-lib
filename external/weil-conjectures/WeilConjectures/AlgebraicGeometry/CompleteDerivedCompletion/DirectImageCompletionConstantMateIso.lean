/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
import all WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Invertibility of the constant direct-image mate

The exact constant-tower comparison is invertible by the unbounded exact
adjunction square and its K-injective normalization.
(blueprint: aux-weil-pbc-direct-image-constant-mate-iso)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The mate of the constant/pullback interchange is an isomorphism.  The
proof uses the K-injective representative normalization of the right-derived
constant-tower square; the mate is invertible on representatives and hence on
all derived objects.
(blueprint: aux-weil-pbc-direct-image-constant-mate-iso) -/
theorem directImage_constant_mate_isIso :
    IsIso ((mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
      (.mk _ _ _ _ (constantInterchange l E
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv))) := by
  have h := CategoryTheory.UnboundedExactTower.constant_isIso
    (CondensedRing.upperStarLowerStarAdjunction
      (DerivedNakayama.integerRing l E) f)
  have hi : (constantInterchange l E
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).inv =
      (CategoryTheory.UnboundedExactTower.constantInterchange
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).hom := by
    ext K
    simp only [constantInterchange, CategoryTheory.UnboundedExactTower.constantInterchange]
    simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.mapDerivedCategoryNatIso_symm, Iso.symm_hom]
    simp
  convert h using 1
  ext K
  rw [hi]
  simp [CategoryTheory.UnboundedExactTower.constantComparison, moduleAdjunction,
    towerAdjunction]

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
