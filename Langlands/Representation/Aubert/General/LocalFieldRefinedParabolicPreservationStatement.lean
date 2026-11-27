import Langlands.AllField.Representation.Geometric.RefinementFunctorsSupplement
import Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor

/-! Finite length and exactness for normalized parabolic functors inside a matrix Levi. -/

namespace Langlands.Aubert.General.RationalPointFamily.GL

open Geometric SmoothRep

universe u v

/-- Both normalized refinement functors preserve finite length and short
exact sequences of finite-length objects for every standard product Levi. -/
def LocalFieldRefinedParabolicPreservationStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ)
    (B : GeneralLinear.BlockShape n) (S : BlockRefinement B),
    letI := T.topology
    let i := T.normalizedRefinedInductionFunctor.{u, max (u + 1) v} B S
    let r := T.normalizedRefinedJacquetFunctor.{u, max (u + 1) v} B S
    PreservesFiniteLength i ∧ PreservesFiniteLengthShortExact i ∧
      PreservesFiniteLength r ∧ PreservesFiniteLengthShortExact r

end Langlands.Aubert.General.RationalPointFamily.GL
