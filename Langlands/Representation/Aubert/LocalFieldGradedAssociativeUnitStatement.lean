import Langlands.Representation.Aubert.LocalFieldGradedGrothendieck

/-! Associativity and the unit identities of exact graded GL induction. -/

namespace Langlands.Aubert.LocalFieldGraded

universe uF uV

/-- Associativity and both unit laws on the entire graded exact Grothendieck
group over every nonarchimedean local field. -/
def LocalFieldGradedAssociativeUnitStatement : Prop :=
  ∀ (K : AllFieldBZ.LocalFieldPackage.{uF}) (T : K.TopologicalData)
    (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV}),
    let m := multiplication T h
    let one := unit T
    (∀ x y z, m (m x y) z = m x (m y z)) ∧
    (∀ x, m one x = x) ∧
    (∀ x, m x one = x)

end Langlands.Aubert.LocalFieldGraded
