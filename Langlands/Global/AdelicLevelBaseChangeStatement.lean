import Langlands.Global.AdelicLevelModelTransition
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Scalar extension of adelic level rings -/

universe u

open IsDedekindDomain
open scoped TensorProduct

namespace Langlands.Global

/-- Enlarging the finite set of places extends scalars from the original S-integers
on the actual full number-field adele levels, including every archimedean factor. -/
def NumberFieldAdelicLevelBaseChangeStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S T : Finset (FinitePlace K)) (hST : S ⊆ T),
    letI := (numberFieldSIntegersMap K hST).toAlgebra
    ∃ e : ((T : Set (FinitePlace K)).integer K) ⊗[((S : Set (FinitePlace K)).integer K)]
        (numberFieldAdeleLevel K S) ≃ₐ[((T : Set (FinitePlace K)).integer K)]
        numberFieldAdeleLevel K T,
      ∀ b a, e (b ⊗ₜ a) =
        numberFieldAdeleLevelDiagonal K T b * numberFieldAdeleLevelMap K hST a

/-- Enlarging a nonempty finite set of places of a global function field extends scalars
on the actual adele levels. The base ring maps are the original inclusions of integer rings. -/
def CurvePlaceAdelicLevelBaseChangeStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S T : Finset (AlgebraicCurve.Place k F)) (_ : S.Nonempty) (hST : S ⊆ T),
    letI := (curvePlaceSIntegersMap k F hST).toAlgebra
    ∃ e : curvePlaceSIntegers k F T ⊗[curvePlaceSIntegers k F S]
        (curvePlaceAdeleLevel k F S) ≃ₐ[curvePlaceSIntegers k F T]
        curvePlaceAdeleLevel k F T,
      ∀ b a, e (b ⊗ₜ a) =
        curvePlaceAdeleLevelDiagonal k F T b * curvePlaceAdeleLevelMap k F hST a

/-- The arithmetic base-change identity for adelic level rings over global fields. -/
def AdelicLevelBaseChangeStatement : Prop :=
  NumberFieldAdelicLevelBaseChangeStatement.{u} ∧ CurvePlaceAdelicLevelBaseChangeStatement.{u}

end Langlands.Global
