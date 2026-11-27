import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement
import Langlands.Representation.Aubert.General.PadicMatrixFunctorSpecializationStatement

/-! The same unadjusted matrix Aubert operator in the two field interfaces. -/

namespace Langlands.Aubert.General.RationalPointFamily.GL

universe u v

/-- Every rank of the local-field matrix alternating sum specializes to the
existing p-adic alternating sum on the same exact group. -/
def PadicMatrixAlternatingOperatorSpecializationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    LocalFieldMatrixParabolicExactLength.{u, v} T.toLocalFieldData n ∧
      ∀ h : LocalFieldMatrixParabolicExactLength.{u, v} T.toLocalFieldData n,
        localFieldMatrixAlternatingOperator T.toLocalFieldData n h =
          Aubert.alternatingOperator.{u, max (u + 1) v} F T n

end Langlands.Aubert.General.RationalPointFamily.GL
