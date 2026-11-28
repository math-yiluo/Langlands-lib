import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement
import Langlands.Representation.Aubert.JacquetCompatibilityStatement
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.CuspidalSupport.LeviGrothendieckTransport

/-! The reversed-Levi Jacquet formula when the reversed object is quasicuspidal. -/

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GeneralLinear Geometric CuspidalSupport SmoothRep
open SmoothRep.FiniteLengthGrothendieckGroup

universe u v

/-- If the actual reversed Jacquet object is quasicuspidal, its transported class
with the Levi sign computes the Jacquet class after matrix Aubert duality. -/
def LocalFieldMatrixQuasicuspidalJacquetExchangeStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ), 0 < n →
    ∀ (h : LocalFieldMatrixParabolicExactLength.{u,v} T n) (C : BlockShape n),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (A : SmoothRep.{0,u,max (u + 1) v} ℂ (GeneralLinear n F)) (hA : A.HasFiniteLength),
      let J := (T.normalizedJacquetFunctor C.reverse).obj A
      IsLeviQuasicuspidal C.reverse J.representation →
      let hw := conjugatesLevi_reversePermutation F C
      let X := (transportFunctor C.reverse C C.reversePermutation hw).obj J
      let hX := transportFunctor_preservesFiniteLength F C.reverse C C.reversePermutation hw J
        ((h C.reverse).2.2.1 A hA)
      (map (T.normalizedJacquetFunctor C) (h C).2.2.1 (h C).2.2.2)
        (localFieldMatrixAlternatingOperator T n h (ofRepresentation A hA)) =
          (-1 : ℤ) ^ (n - C.length) • ofRepresentation X hX

end Langlands.Aubert.General.RationalPointFamily.GL
