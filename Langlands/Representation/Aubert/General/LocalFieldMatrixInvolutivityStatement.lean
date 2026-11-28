import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement

/-! Involutivity of the unadjusted matrix Aubert operator over a local field. -/

namespace Langlands.Aubert.General.RationalPointFamily.GL

universe u v

/-- The actual unadjusted matrix Aubert operator squares to the identity,
with the finite-length and exactness witnesses supplied in every rank. -/
def LocalFieldMatrixInvolutivityStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ),
    letI := T.topology
    ∃ h : LocalFieldMatrixParabolicExactLength.{u, v} T n,
      let D := localFieldMatrixAlternatingOperator T n h
      D.comp D = LinearMap.id

end Langlands.Aubert.General.RationalPointFamily.GL
