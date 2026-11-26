import Langlands.Representation.Aubert.LanglandsHeadDuality
import Langlands.Representation.Classification.TemperedSpecialSegmentRefinementProof

/-! # Strict descent for constituents of a tempered standard head kernel -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory Classification GeneralLinear PadicField.TopologicalData
open SmoothRep SmoothRep.IrreducibleGrothendieckProof VirtualRepresentation
open Aubert Aubert.SegmentPolynomialSurjectivity Aubert.LanglandsHeadDuality

universe uF uV

/-- Refinement of an ordered tempered standard module identifies its head
multisegment and places every irreducible constituent of its head kernel
strictly below it in the well-founded rank order. -/
def TemperedLanglandsHeadOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (t : T.TemperedLanglandsDatum.{max uF uV} n)
        (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
        t.IsLanglandsHead π →
        ∃ a : T.Multisegment.{max uF uV, uF}, a.IsLanglandsHead π ∧
          t.standardModule.HasFiniteLength ∧
          ∀ (b : T.Multisegment.{max uF uV, uF})
            (D : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
            b.IsLanglandsHead D →
            IsSubquotient D (t.standardModule.subrepresentation
              (headKernel t.standardModule.representation)) →
            b.RankLE a ∧ b ≠ a

set_option maxHeartbeats 800000 in
/-- Use the ordinary composition multiplicities of the standard module.
The coefficient on the head is one, and Aubert duality transports the
rank-order bounds from the segment monomials to the special-block product. -/
theorem temperedLanglandsHeadOrder : TemperedLanglandsHeadOrderStatement.{uF,uV} := by
  intro p _ F T
  let := T.topology
  intro n hn t π hhead
  obtain ⟨d, hOrdered, hSpecial, ⟨e⟩⟩ :=
    temperedSpecialSegmentRefinement.{uF,uV} F T n hn t
  let a := d.multisegment
  have ha : a.IsLanglandsHead π :=
    ⟨d, rfl, hOrdered, hSpecial, hhead.of_equiv (SmoothRep.equivOfIso e.symm)⟩
  have hDfin : d.induced.HasFiniteLength :=
    hasFiniteLength_induced_of_irreducible F T d fun i =>
      isIrreducible_of_isSegmentHead F T (hSpecial i)
  let B := t.standardModule
  have hBfin : B.HasFiniteLength :=
    Derivative.ProductDerivativesFiniteLength.hasFiniteLength_of_iso e hDfin
  refine ⟨a, ha, hBfin, ?_⟩
  let S := headKernel B.representation
  let K := B.subrepresentation S
  let i := SmoothRep.hom (B.subtype S)
  have hi := B.subtype_injective S
  have hKfin : K.HasFiniteLength := hBfin.of_injective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ i) hi
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  let hx := binaryProductExactness.{uF,uV} F T
  let hl := gradedInductionRingLaws.{uF,uV} F T hx
  intro b D hb hK
  have hDirr : D.IsIrreducible := isIrreducible_of_isLanglandsHead F T hb
  let cD := GeneralLinear.irreducibleIsoClass n F.Carrier D hDirr
  obtain ⟨c, hc⟩ := exists_isLabel_of_degree F T b (degree_of_isLanglandsHead F T hb)
  have hAubert : gradedAdjustedOperator F T (basisClass F T n c) = basisClass F T n cD :=
    gradedAdjustedOperator_label F T hx hl ψ b n c hc D hDirr hb
  have hDual : gradedAdjustedOperator F T (basisClass F T n cD) = basisClass F T n c := by
    rw [← hAubert, adjustedInvolutivity]
  have hcoeff := coeff_gradedAdjustedOperator F T hDual
    (gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier d.induced hDfin))
  rw [gradedAdjustedOperator_headInduced F T hx hl d hSpecial hDfin,
    coeff_gradedInclusion_ofRepresentation F T n _ hDfin D hDirr] at hcoeff
  have hmul :
      (compositionMultiplicity ⟨d.induced, hDfin⟩ D : ℤ) =
        (compositionMultiplicity ⟨B, hBfin⟩ D : ℤ) := by
    rw [← compositionFactors_apply _ D hDirr, ← compositionFactors_apply _ D hDirr]
    exact congrArg (fun f => f (SmoothRep.irreducibleIsoClass D hDirr))
      (compositionFactors_eq_of_equiv ⟨d.induced, hDfin⟩ ⟨B, hBfin⟩ (SmoothRep.equivOfIso e))
  rw [hmul] at hcoeff
  obtain ⟨W, j, q, hj, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hK
  have hB : IsSubquotient D B := SmoothRep.isSubquotient_iff_exists.mpr
    ⟨W, j ≫ B.subtype S, q, hi.comp hj, hq⟩
  have hpos : 0 < compositionMultiplicity ⟨B, hBfin⟩ D :=
    (compositionMultiplicity_pos_iff_isSubquotient ⟨B, hBfin⟩ D hDirr).mpr hB
  have hpos' : 0 < coeff F T n c (zeta F T hx hl a) := by
    change 0 < coeff F T n c (zeta F T hx hl d.multisegment)
    rw [hcoeff]
    exact_mod_cast hpos
  refine ⟨rankLE_of_coeff_zeta_pos F T hx hl ψ (highestDerivativeLabelStep F T ψ)
    n c b a hc hpos', ?_⟩
  intro he
  subst b
  have hone : (compositionMultiplicity ⟨B, hBfin⟩ D : ℤ) = 1 :=
    hcoeff.symm.trans (coeff_zeta_eq_one_of_isLabel F T hx hl ψ hc)
  obtain ⟨eD⟩ := (multisegmentHeadClassification F T n a a π D ha hb).mp rfl
  obtain ⟨hπirr, qπ, hqπ, _⟩ := id hhead
  have hExact : SmoothRep.IsShortExact i qπ := by
    refine ⟨hi, hqπ, ?_⟩
    change LinearMap.range S.toSubmodule.subtype = LinearMap.ker qπ.toLinearMap
    rw [Submodule.range_subtype, hhead.headKernel_eq π.representation hπirr qπ hqπ]
  let hπfin := hasFiniteLength_of_isIrreducible hπirr
  have hAdd := congrArg (fun f => f (SmoothRep.irreducibleIsoClass D hDirr))
    (compositionFactors_shortExact ⟨K, hKfin⟩ ⟨B, hBfin⟩ ⟨π, hπfin⟩ i qπ hExact)
  have hπval : (compositionMultiplicity ⟨π, hπfin⟩ D : ℤ) = 1 := by
    rw [← compositionFactors_apply _ D hDirr,
      compositionFactors_irreducible π hπirr hπfin,
      irreducibleIsoClass_eq_of_equiv hπirr hDirr (SmoothRep.equivOfIso eD)]
    simp [generator]
  change compositionFactors ⟨B, hBfin⟩ (SmoothRep.irreducibleIsoClass D hDirr) =
    (compositionFactors ⟨K, hKfin⟩ + compositionFactors ⟨π, hπfin⟩)
      (SmoothRep.irreducibleIsoClass D hDirr) at hAdd
  simp only [Finsupp.add_apply, compositionFactors_apply, hone, hπval] at hAdd
  have hKpos := (compositionMultiplicity_pos_iff_isSubquotient ⟨K, hKfin⟩ D hDirr).mpr hK
  omega

end Langlands.BaseChange
