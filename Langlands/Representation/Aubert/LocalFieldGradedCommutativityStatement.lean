import Langlands.Representation.Aubert.LocalFieldGradedGrothendieck

/-! Commutativity of the exact graded GL induction product. -/

namespace Langlands.Aubert.LocalFieldGraded

universe uF uV

/-- The binary normalized product is commutative on the whole graded exact
Grothendieck group over any nonarchimedean local field. -/
def LocalFieldGradedCommutativityStatement : Prop :=
  ∀ (K : AllFieldBZ.LocalFieldPackage.{uF}) (T : K.TopologicalData)
    (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV}),
    let m := multiplication T h
    ∀ x y, m x y = m y x

end Langlands.Aubert.LocalFieldGraded
