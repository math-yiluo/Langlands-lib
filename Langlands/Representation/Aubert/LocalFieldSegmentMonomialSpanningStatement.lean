import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts
import Langlands.Representation.Aubert.LocalFieldGradedGrothendieck
import Langlands.Representation.Smooth.IrreducibleRealization

/-! Additive spanning by actual segment induction monomials. -/

noncomputable section

namespace Langlands.Aubert.LocalFieldGraded

open GeneralLinear
open AllFieldBZ (LocalFieldPackage)
open AllFieldBZ.LocalFieldPackage.TopologicalData

universe uF uV

variable {K : LocalFieldPackage.{uF}} (T : K.TopologicalData)

/-- An actual choice of the socle belonging to a Zelevinsky segment. -/
abbrev ActualSegmentSocle :=
  letI := T.topology
  (Δ : Segment.{max uF uV,uF} T) ×
    {π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree K.Carrier) //
      T.IsSegmentSocle Δ π}

/-- The actual socle class included in its rank summand. -/
def segmentSocleGenerator (A : ActualSegmentSocle.{uF,uV} T) :
    GradedGrothendieckGroup.{uF,uV} T :=
  letI := T.topology
  inclusion T A.1.degree
    (finiteLengthClass A.1.degree K.Carrier A.2.val
      (SmoothRep.hasFiniteLength_of_isIrreducible (by
        obtain ⟨_, _, hs⟩ := A.2.property
        exact hs.1)))

/-- A finite product of actual segment socle classes, with the empty product
given by the trivial rank-zero line. -/
def segmentSocleMonomial
    (h : LocalFieldBinaryProductExactLengthStatement.{uF,uV})
    (L : List (ActualSegmentSocle.{uF,uV} T)) :
    GradedGrothendieckGroup.{uF,uV} T :=
  letI := T.topology
  L.foldr (fun A x => multiplication T h (segmentSocleGenerator T A) x) (unit T)

/-- The finite segment induction monomials span the entire exact graded group
over the integers. -/
def LocalFieldSegmentMonomialSpanningStatement : Prop :=
  ∀ (K : LocalFieldPackage.{uF}) (T : K.TopologicalData)
    (h : LocalFieldBinaryProductExactLengthStatement.{uF,uV}),
    letI := T.topology
    Submodule.span ℤ (Set.range (segmentSocleMonomial T h)) = ⊤

end Langlands.Aubert.LocalFieldGraded
