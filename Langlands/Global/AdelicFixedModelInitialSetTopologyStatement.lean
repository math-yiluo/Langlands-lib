import Langlands.Global.AdelicFixedModelInitialSet
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.NumberTheory.FunctionField

/-! # Initial-set independence of actual arithmetic adelic point topologies -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Enlarging the initial set preserves the original function-field point topology. -/
def CurvePlaceFixedModelInitialSetTopologyStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S U : Finset (AlgebraicCurve.Place k F)) (hSU : S ⊆ U)
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := curvePlaceFixedModelAdelePointTopology k F S X
    letI := curvePlaceFixedModelAdelePointTopology k F U
      (curvePlaceLevelModelBaseChange k F hSU X)
    IsHomeomorph (curvePlaceFixedModelInitialSetEquiv k F hSU X)

/-- Enlarging the initial finite set preserves the full number-field point topology. -/
def NumberFieldFixedModelInitialSetTopologyStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S U : Finset (FinitePlace K)) (hSU : S ⊆ U)
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    letI := numberFieldFixedModelAdelePointTopology K S X
    letI := numberFieldFixedModelAdelePointTopology K U
      (numberFieldLevelModelBaseChange K hSU X)
    IsHomeomorph (numberFieldFixedModelInitialSetEquiv K hSU X)

/-- The actual initial-set comparison is a homeomorphism in both arithmetic settings. -/
def AdelicFixedModelInitialSetTopologyStatement : Prop :=
  CurvePlaceFixedModelInitialSetTopologyStatement.{u} ∧
    NumberFieldFixedModelInitialSetTopologyStatement.{u}

end Langlands.Global
