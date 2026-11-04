import Langlands.Global.AdelicSIntegersDiagram
import Mathlib.NumberTheory.FunctionField

/-! # Exhaustion and algebra-colimit targets for the actual integer rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Global

/-- The actual function field is exhausted by its integer stages and is their colimit. -/
def CurvePlaceSIntegersColimitStatement : Prop :=
  ∀ (k F : Type u) [Field k] [PerfectField k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)),
    (∀ x : F, ∃ T : AdelicLevelIndexAbove S, x ∈ curvePlaceSIntegers k F T.val) ∧
      Nonempty (IsColimit (curvePlaceSIntegersOverCocone k F S))

/-- The original number field is exhausted by its integer stages and is their colimit. -/
def NumberFieldSIntegersColimitStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    (∀ x : K, ∃ T : AdelicLevelIndexAbove S,
      x ∈ (T.val : Set (FinitePlace K)).integer K) ∧
      Nonempty (IsColimit (numberFieldSIntegersOverCocone K S))

/-- Both actual arithmetic integer-ring colimits, over every original initial base. -/
def AdelicSIntegersColimitStatement : Prop :=
  CurvePlaceSIntegersColimitStatement.{u} ∧ NumberFieldSIntegersColimitStatement.{u}

end Langlands.Global
