import Langlands.Representation.Aubert.LocalFieldGradedAdjustedOperator

/-! Multiplicativity of the actual adjusted Aubert operator on the graded group. -/

namespace Langlands.Aubert.LocalFieldGraded

open General.RationalPointFamily.GL
open AllFieldBZ (LocalFieldPackage)

universe u v

/-- The adjusted Aubert operator preserves the unit and normalized induction
multiplication on the whole graded exact Grothendieck group. -/
def LocalFieldGradedAdjustedMultiplicativityStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F),
    letI : TopologicalSpace (LocalFieldPackage.ofField F).Carrier := T.topology
    ∃ (hx : LocalFieldBinaryProductExactLengthStatement.{u, max (u + 1) v})
      (h : ∀ n, LocalFieldMatrixParabolicExactLength.{u, v} T n),
      let d := gradedAdjustedOperator.{u, v} T h
      let m := multiplication.{u, max (u + 1) v} (K := LocalFieldPackage.ofField F) T hx
      let one := unit.{u, max (u + 1) v} (K := LocalFieldPackage.ofField F) T
      d one = one ∧
        ∀ x y, d (m x y) = m (d x) (d y)

end Langlands.Aubert.LocalFieldGraded
