/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso
public import WeilConjectures.AlgebraicGeometry.SfP1ProjectionTraceFalseChartPasting

/-! # Inverse of the false projection chart factor -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

@[irreducible]
def falseProjectionChartFactorInv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) ⟶
      (ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteP1SplittingTarget A N hA S) := by
  letI := isIso_ordinaryFiniteP1Exchange A (ProjectiveLine S ↘ S)
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
  exact
    (ordinaryFinitePushforward A
      (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
      (ordinaryFiniteShiftedLinePullback A N hA t
        (ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S))
        (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).inv ≫
      inv (ordinaryFiniteP1Exchange A (ProjectiveLine S ↘ S)
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))

/--
The chart factor and its displayed inverse cancel by the two inverse/direct-image
cancellations.  This is the cancellation step after the false-projection
mate-pasting calculation.
(auxiliary; not a blueprint node)
-/
theorem falseProjectionChartFactor_cancel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    falseProjectionChartFactor A N hA t S hS ≫
        falseProjectionChartFactorInv A N hA t S hS = 𝟙 _ := by
  let := isIso_ordinaryFiniteP1Exchange A (ProjectiveLine S ↘ S)
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
  unfold falseProjectionChartFactor falseProjectionChartFactorInv
  simp only [Category.assoc, Iso.hom_inv_id_map_assoc, IsIso.hom_inv_id]

end AlgebraicGeometry.Etale.SfP1Transport
