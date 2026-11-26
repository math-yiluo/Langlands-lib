import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement

/-! Finite-length and exactness inputs for all matrix Aubert operators. -/

namespace Langlands.Aubert.General.RationalPointFamily.GL

universe u v

/-- In every rank over every nonarchimedean local field, the actual normalized
matrix induction and Jacquet functors preserve finite length and short exact
sequences of finite-length objects. -/
def LocalFieldMatrixParabolicPreservationStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ),
    LocalFieldMatrixParabolicExactLength.{u, v} T n

end Langlands.Aubert.General.RationalPointFamily.GL
