import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement
import Langlands.Representation.CuspidalSupport.LeviDefinitions

/-! Classes of induction after Jacquet on a quasicuspidal induction. -/

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GeneralLinear SmoothRep CuspidalSupport
open SmoothRep.FiniteLengthGrothendieckGroup

universe u v

/-- For a quasicuspidal inducing object, each induction–Jacquet term on its
ambient induction has class a natural multiple of the original class. -/
def LocalFieldMatrixQuasicuspidalCutClassStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ), 0 < n →
    ∀ (B C : BlockShape n),
      letI := T.topology
      ∃ h : LocalFieldMatrixParabolicExactLength.{u, v} T n,
        let i (D : BlockShape n) := map (T.normalizedParabolicInductionFunctor D) (h D).1 (h D).2.1
        let r := map (T.normalizedJacquetFunctor C) (h C).2.2.1 (h C).2.2.2
        ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (B.Levi F)) (hA : A.HasFiniteLength),
          IsLeviQuasicuspidal B A.representation →
          let x := i B (ofRepresentation A hA)
          ∃ m : ℕ, i C (r x) = m • x

end Langlands.Aubert.General.RationalPointFamily.GL
