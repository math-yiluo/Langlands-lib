import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentDiagram
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentCover

/-! # Comparison of the strict and relative binary Laurent diagrams: target -/

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

/-- The actual strict binary Laurent quotients and their actual four-variable
intersection quotient are boundedly equivalent to the actual relative upper, lower
and two-variable overlap quotients over the radius-one presentation, compatibly
with the coefficient maps and with both overlap arrows. -/
def BinaryLaurentDiagramComparisonStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (f : P),
    let A := PresentedAffinoidAlgebra.ofStrict K P
    let e := PresentedAffinoidAlgebra.strictEquiv K P
    let fRel : A := e.symm f
    let dUpper := laurentUpper f
    let dLower := laurentLower f
    ∃ (eUpper : BoundedAlgEquiv K dUpper.algebra
        (PresentedAffinoidAlgebra.BinaryLaurent.Upper K A fRel))
      (eLower : BoundedAlgEquiv K dLower.algebra
        (PresentedAffinoidAlgebra.BinaryLaurent.Lower K A fRel))
      (eOverlap : BoundedAlgEquiv K (dUpper.inter dLower).algebra
        (PresentedAffinoidAlgebra.BinaryLaurent.Overlap K A fRel)),
      (∀ a : P, eUpper (dUpper.baseMap a) =
        PresentedAffinoidAlgebra.BinaryLaurent.upperBase K A fRel (e.symm a)) ∧
      (∀ a : P, eLower (dLower.baseMap a) =
        PresentedAffinoidAlgebra.BinaryLaurent.lowerBase K A fRel (e.symm a)) ∧
      (∀ a : P, eOverlap ((dUpper.inter dLower).baseMap a) =
        PresentedAffinoidAlgebra.BinaryLaurent.overlapBase K A fRel (e.symm a)) ∧
      (∀ sUpper : dUpper.algebra,
        eOverlap ((interLeft dUpper dLower).restriction sUpper) =
          PresentedAffinoidAlgebra.BinaryLaurent.left K A fRel (eUpper sUpper)) ∧
      (∀ sLower : dLower.algebra,
        eOverlap ((interRight dUpper dLower).restriction sLower) =
          PresentedAffinoidAlgebra.BinaryLaurent.right K A fRel (eLower sLower))

end Langlands.Analytic.StrictTestDomain
