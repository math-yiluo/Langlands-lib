import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts
import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement
import Langlands.Representation.Aubert.LocalFieldSupportSign

/-! The actual unadjusted and support-adjusted segment exchange. -/

namespace Langlands.Aubert.LocalFieldGraded

open AllFieldBZ (LocalFieldPackage)
open AllFieldBZ.LocalFieldPackage.TopologicalData
open General.RationalPointFamily.GL
open SmoothRep.FiniteLengthGrothendieckGroup

universe u v

/-- Aubert's unadjusted operator exchanges the two actual segment endpoint
classes with the Levi sign. The support-adjusted operator exchanges them
without a sign. -/
def LocalFieldSegmentExchangeStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F),
    let K := LocalFieldPackage.ofField F
    letI : TopologicalSpace K.Carrier := T.topology
    ∀ (Δ : @Segment.{max (u + 1) v,u} K T)
      (πZ πS : SmoothRep.{0,u,max (u + 1) v} ℂ (GeneralLinear Δ.degree K.Carrier)),
      IsSegmentSocle (F := K) T Δ πZ → IsSegmentHead (F := K) T Δ πS →
      ∀ (hZ : πZ.HasFiniteLength) (hS : πS.HasFiniteLength)
        (h : LocalFieldMatrixParabolicExactLength.{u,v} T Δ.degree),
      let z := ofRepresentation πZ hZ
      let s := ofRepresentation πS hS
      let ε : ℤ := (-1) ^ (Δ.degree - Δ.length)
      let D := localFieldMatrixAlternatingOperator T Δ.degree h
      let I := adjustOperator.{u,max (u + 1) v} (K := K) T Δ.degree D
      D z = ε • s ∧ D s = ε • z ∧ I z = s ∧ I s = z

end Langlands.Aubert.LocalFieldGraded
