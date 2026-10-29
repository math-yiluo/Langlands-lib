import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Representation.Filtration.MultiplicityStatement

/-! A derived criterion for actual ordered Jacquet equivalences. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uA uW uZ

/-- Evaluation identifies the first length-one Jacquet module, and exact
multiplicity one identifies the complementary quotient. All hypotheses remain
obligations of an application to actual parabolic induction. -/
def NormalizedJacquetOrderedLengthOneCriterion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (A : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n F.Carrier))
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (Z : Type uZ) [AddCommGroup Z] [Module ℂ Z]
      (σ : Representation ℂ (B.Levi F.Carrier) W)
      (τ : Representation ℂ (B.Levi F.Carrier) Z),
      σ.IsIrreducible → τ.IsIrreducible → ¬ Nonempty (σ.Equiv τ) →
      ∀ (S : Subrepresentation A.representation)
        (f : (SmoothRep.subrepresentation A S).representation.IntertwiningMap
          (T.normalizedParabolicInduced B σ)), f ≠ 0 →
        repLength (((T.normalizedJacquetFunctor B).obj
          (SmoothRep.subrepresentation A S)).representation) = 1 →
        repLength (((T.normalizedJacquetFunctor B).obj
          (SmoothRep.quotient A S)).representation) = 1 →
        HasJordanHolderMultiplicity
          (Rep.of (((T.normalizedJacquetFunctor B).obj A).representation))
          (Rep.of τ) 1 →
        Nonempty ((((T.normalizedJacquetFunctor B).obj
          (SmoothRep.subrepresentation A S)).representation).Equiv σ) ∧
        Nonempty ((((T.normalizedJacquetFunctor B).obj
          (SmoothRep.quotient A S)).representation).Equiv τ)

end Langlands.CuspidalSupport
