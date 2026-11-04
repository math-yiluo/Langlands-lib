import Langlands.Global.AdelicFixedModelCocone
import Mathlib.NumberTheory.FunctionField
import Mathlib.Topology.Bases

/-! # Second countability of actual full-adele model points -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Full-adele points of finite-type models over function-field integer rings. -/
def CurvePlaceFixedModelSecondCountabilityStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    @SecondCountableTopology (CurvePlaceFixedModelAdelePoints k F S X)
      (curvePlaceFixedModelAdelePointTopology k F S X)

/-- Full-adele points of number-field models, including every infinite factor. -/
def NumberFieldFixedModelSecondCountabilityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom],
    @SecondCountableTopology (NumberFieldFixedModelAdelePoints K S X)
      (numberFieldFixedModelAdelePointTopology K S X)

/-- Finite-type arithmetic models have second-countable full-adele points in
their actual stage-final topology, without a separation hypothesis. -/
def AdelicFixedModelSecondCountabilityStatement : Prop :=
  CurvePlaceFixedModelSecondCountabilityStatement.{u} ∧
    NumberFieldFixedModelSecondCountabilityStatement.{u}

end Langlands.Global
