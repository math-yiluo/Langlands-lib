import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentDiagramComparisonStatement
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentDiagramCompatibility
import Langlands.Geometry.Analytic.RationalLocalization.RelativeComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentOverlapComparison

/-! # Comparison of the actual strict and relative binary Laurent diagrams -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData PresentedAffinoidAlgebra

/-- The three actual quotient equivalences, their three coefficient laws and
their two restriction laws hold simultaneously, without a valuation or
nonzero-quotient hypothesis. -/
theorem binaryLaurentDiagramComparison :
    BinaryLaurentDiagramComparisonStatement.{u} := by
  intro K _ _ _ P f
  let A := ofStrict K P
  let e := strictEquiv K P
  let fRel : A := e.symm f
  let dUpper := laurentUpper f
  let dLower := laurentLower f
  let dOverlap := dUpper.inter dLower

  have hOne : e.symm (1 : P) = (1 : A) :=
    e.symm.toAlgEquiv.map_one
  have hOnes : (fun _ : Fin 1 => e.symm (1 : P)) = (fun _ => (1 : A)) :=
    funext fun _ => hOne
  have hDen : e.symm dOverlap.denominator = fRel := by
    exact congrArg e.symm (laurent_inter_denominator K P f)
  have hNum : (fun j => e.symm (dOverlap.numerator j)) =
      BinaryLaurent.productNumerators K A fRel := by
    change (fun j => (strictEquiv K P).symm
      (((laurentUpper f).inter (laurentLower f)).numerator j)) =
      ![(strictEquiv K P).symm f, 1,
        ((strictEquiv K P).symm f) ^ 2, (strictEquiv K P).symm f]
    exact laurent_inter_numerator_strictEquiv K P f

  let cUpper := relativeRationalEquivOfEq K A 1
    (g := e.symm (1 : P)) (h := (1 : A))
    (n := fun _ => e.symm f) (k := fun _ => fRel) hOne rfl
  let cLower := relativeRationalEquivOfEq K A 1
    (g := e.symm f) (h := fRel)
    (n := fun _ => e.symm (1 : P)) (k := fun _ => (1 : A)) rfl hOnes
  let cOverlap := relativeRationalEquivOfEq K A 4 hDen hNum

  let eUpper : BoundedAlgEquiv K dUpper.algebra (BinaryLaurent.Upper K A fRel) :=
    (RationalLocalization.relativeEquiv K P 1 1 (fun _ => f)).trans cUpper
  let eLower : BoundedAlgEquiv K dLower.algebra (BinaryLaurent.Lower K A fRel) :=
    (RationalLocalization.relativeEquiv K P 1 f (fun _ => 1)).trans cLower
  let eOverlap : BoundedAlgEquiv K dOverlap.algebra (BinaryLaurent.Overlap K A fRel) :=
    (RationalLocalization.relativeEquiv K P dOverlap.arity
      dOverlap.denominator dOverlap.numerator).trans
      (cOverlap.trans (BinaryLaurent.productOverlapEquiv K A fRel))

  have hUpper (a : P) : eUpper (dUpper.baseMap a) =
      BinaryLaurent.upperBase K A fRel (e.symm a) := by
    change cUpper (RationalLocalization.relativeEquiv K P 1 1 (fun _ => f)
      (RationalLocalization.baseMap K P 1 1 (fun _ => f) a)) = _
    rw [RationalLocalization.relativeEquiv_baseMap]
    exact relativeRationalEquivOfEq_baseMap K A 1 hOne rfl (e.symm a)
  have hLower (a : P) : eLower (dLower.baseMap a) =
      BinaryLaurent.lowerBase K A fRel (e.symm a) := by
    change cLower (RationalLocalization.relativeEquiv K P 1 f (fun _ => 1)
      (RationalLocalization.baseMap K P 1 f (fun _ => 1) a)) = _
    rw [RationalLocalization.relativeEquiv_baseMap]
    exact relativeRationalEquivOfEq_baseMap K A 1 rfl hOnes (e.symm a)
  have hOverlap (a : P) : eOverlap (dOverlap.baseMap a) =
      BinaryLaurent.overlapBase K A fRel (e.symm a) := by
    change BinaryLaurent.productOverlapEquiv K A fRel
      (cOverlap (RationalLocalization.relativeEquiv K P dOverlap.arity
        dOverlap.denominator dOverlap.numerator
        (RationalLocalization.baseMap K P dOverlap.arity
          dOverlap.denominator dOverlap.numerator a))) = _
    rw [RationalLocalization.relativeEquiv_baseMap]
    change BinaryLaurent.productOverlapEquiv K A fRel
      (relativeRationalEquivOfEq K A 4 hDen hNum
        (RelativeRationalPresentation.baseMap K A (PositivePolyradius.unit (Fin 4))
          (e.symm dOverlap.denominator) (fun j => e.symm (dOverlap.numerator j))
          (e.symm a))) = _
    exact (congrArg (BinaryLaurent.productOverlapEquiv K A fRel)
      (relativeRationalEquivOfEq_baseMap K A 4 hDen hNum (e.symm a))).trans
      (BinaryLaurent.productOverlapEquiv_baseMap K A fRel (e.symm a))

  refine ⟨eUpper, eLower, eOverlap, hUpper, hLower, hOverlap, ?_, ?_⟩
  · intro sUpper
    exact congrArg
      (fun ψ : BoundedAlgHom K dUpper.algebra (BinaryLaurent.Overlap K A fRel) =>
        ψ sUpper)
      (binaryLaurent_left_square K P f eUpper.toBoundedAlgHom
        eOverlap.toBoundedAlgHom hUpper hOverlap)
  · intro sLower
    exact congrArg
      (fun ψ : BoundedAlgHom K dLower.algebra (BinaryLaurent.Overlap K A fRel) =>
        ψ sLower)
      (binaryLaurent_right_square K P f eLower.toBoundedAlgHom
        eOverlap.toBoundedAlgHom hLower hOverlap)

end Langlands.Analytic.StrictTestDomain
