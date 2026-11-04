import Langlands.Global.AdelicLevelModelTopology

/-! # Functoriality of actual adelic-level model point topologies -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Actual model morphisms act continuously on curve-place and full
number-field adelic-level points, with their original induced topologies. -/
def AdelicLevelModelFunctorialityStatement : Prop :=
  (∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) (f : X ⟶ Y),
    Continuous[curvePlaceLevelModelPointTopology k F S X,
      curvePlaceLevelModelPointTopology k F S Y]
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S)))) ∧
  (∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (f : X ⟶ Y),
    Continuous[numberFieldLevelModelPointTopology K S X,
      numberFieldLevelModelPointTopology K S Y]
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
        (numberFieldAdeleLevel K S) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (numberFieldAdeleLevel K S))))

end Langlands.Global
