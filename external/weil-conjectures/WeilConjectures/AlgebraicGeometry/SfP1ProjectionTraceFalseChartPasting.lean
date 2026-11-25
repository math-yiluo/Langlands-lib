/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1ChartExchange

/-! # Mate-pasting factor for the false projective-line projection -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The ordinary exchange factor occurring after the false projection exchange. -/
@[irreducible]
def falseProjectionChartFactor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj
        (ordinaryFiniteP1SplittingTarget A N hA S) ⟶
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  ordinaryFiniteP1Exchange A (ProjectiveLine S ↘ S)
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    (ordinaryFinitePushforward A
      (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
      (ordinaryFiniteShiftedLinePullback A N hA t
        (ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S))
        (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).hom

/--
The false projection mate-pasting calculation, before the trace is applied.
It is the chart-exchange factorization precomposed by the intermediate
comparison, and is independent of any choice of trace morphism.
(auxiliary; not a blueprint node)
-/
theorem falseProjectionChartPasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤))) :
    middleComparison A N hA t f i hi hS false ≫
        (ordinaryFinitePullback A i.hom).map
          (projectionExchange A N hA t S hS false) ≫
        (ordinaryFinitePullback A i.hom).map
          (ordinaryFiniteP1Exchange A (ProjectiveLine S ↘ S)
            ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePushforward A
            (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
            (ordinaryFiniteShiftedLinePullback A N hA t
              (ProjectiveSpace.map (ULift.{u} (Fin 2)) (ProjectiveLine S ↘ S))
              (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS)).hom) =
      middleComparison A N hA t f i hi hS false ≫
        (ordinaryFinitePullback A i.hom).map
          (ordinaryFiniteP1DiagonalChartMap A N hA t S hS false) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [chartExchange]

end AlgebraicGeometry.Etale.SfP1Transport
