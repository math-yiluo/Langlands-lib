import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Aubert.RefinedAlternatingOperator

/-!
# Commutation of the actual Aubert operator with normalized induction

This proposition states the first identity in Aubert's Theorem 1.7(2) for
`GL_n` and its actual product Levis. Both operators are unadjusted signed
induction-after-Jacquet sums on the exact finite-length Grothendieck groups.
-/

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Normalized induction intertwines the unadjusted Aubert operators on an
actual product Levi and the ambient general linear group, in every rank. -/
def InductionCommutationStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n),
    (alternatingOperator.{uF, uV} F T n).comp
        (Parabolic.normalizedInductionK0.{uF, uV} F T B) =
      (Parabolic.normalizedInductionK0.{uF, uV} F T B).comp
        (alternatingOperatorOnLevi.{uF, uV} F T B)

end Langlands.Aubert
