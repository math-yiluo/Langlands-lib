import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Category.Subquotients

/-! Irreducible inducing subquotients retaining an actual embedding. -/

namespace Langlands.Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- If an irreducible smooth representation has finite-length normalized
Jacquet module and maps nontrivially into normalized induction of `σ`, then
it embeds into induction of an irreducible actual subquotient of `σ`.
That constituent is a quotient of the whole normalized Jacquet module. -/
def IrreducibleInducingSubquotientStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (σ : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
    π.IsIrreducible →
    ((T.normalizedJacquetFunctor B).obj π).HasFiniteLength →
    (∃ f : π.representation.IntertwiningMap
      (T.normalizedParabolicInduced B σ.representation), f ≠ 0) →
    ∃ ρ : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier),
      ρ.IsIrreducible ∧
      SmoothRep.IsQuotient ρ ((T.normalizedJacquetFunctor B).obj π) ∧
      SmoothRep.IsSubquotient ρ σ ∧
      SmoothRep.IsSubrepresentation π ((T.normalizedParabolicInductionFunctor B).obj ρ)

end Langlands.Parabolic
