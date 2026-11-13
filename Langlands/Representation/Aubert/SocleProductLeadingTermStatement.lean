import Langlands.Representation.Aubert.SegmentPolynomialSurjectivity

/-!
# Rank triangularity and leading multiplicity for products of socle labels

This proposition is a new proof target for the actual normalized-induction
multiplication. It includes every natural rank and keeps the field and
representation-carrier universes independent.
-/

namespace Langlands.Aubert

open PadicField.TopologicalData SegmentPolynomialSurjectivity

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Products of actual socle labels are rank triangular, and the label of the
sum multisegment has coefficient one. The structural witnesses are universally
quantified, and multiplication is the actual bilinear induction map. -/
def SocleProductLeadingTermStatement : Prop :=
  ∀ (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    (_hl : GradedInductionRingLawsStatement F T hx),
    (∀ (a b q : T.Multisegment.{max uF uV, uF}) (m n k : ℕ)
      (c : Label.{uF, uV} F T m) (d : Label.{uF, uV} F T n)
      (e : Label.{uF, uV} F T k),
      IsLabel F T a m c → IsLabel F T b n d → IsLabel F T q k e →
        0 < coeff F T k e
          (gradedMultiplication F T hx (basisClass F T m c) (basisClass F T n d)) →
        Multisegment.RankLE q (a + b)) ∧
    (∀ (a b : T.Multisegment.{max uF uV, uF}) (m n k : ℕ)
      (c : Label.{uF, uV} F T m) (d : Label.{uF, uV} F T n)
      (e : Label.{uF, uV} F T k),
      IsLabel F T a m c → IsLabel F T b n d → IsLabel F T (a + b) k e →
        coeff F T k e
          (gradedMultiplication F T hx (basisClass F T m c) (basisClass F T n d)) = 1)

end Langlands.Aubert
