import Langlands.Global.AdelicFixedModelCocone

/-! # Functoriality of actual full-adele model point topologies -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Actual model morphisms act continuously on full-adele points for the
independently defined final arithmetic topologies. -/
def AdelicFixedModelFunctorialityStatement : Prop :=
  (∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) (f : X ⟶ Y),
    Continuous[curvePlaceFixedModelAdelePointTopology k F S X,
      curvePlaceFixedModelAdelePointTopology k F S Y]
      (fun p : CurvePlaceFixedModelAdelePoints k F S X =>
        (p ≫ f : CurvePlaceFixedModelAdelePoints k F S Y))) ∧
  (∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (f : X ⟶ Y),
    Continuous[numberFieldFixedModelAdelePointTopology K S X,
      numberFieldFixedModelAdelePointTopology K S Y]
      (fun p : NumberFieldFixedModelAdelePoints K S X =>
        (p ≫ f : NumberFieldFixedModelAdelePoints K S Y)))

end Langlands.Global
