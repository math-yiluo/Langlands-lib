import Langlands.Representation.Classification.SpehUnitarizabilityReductionStatement
import Langlands.Representation.Classification.SpehSegmentParameters
import Langlands.Representation.Classification.LanglandsHeadProductSubquotientStatement
import Langlands.Representation.Classification.MultisegmentConstituentRealTwistCompatibilityProof
import Langlands.Representation.Classification.MultisegmentHeadExistenceProof
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterReduction

/-! # The Speh neighbor product at the complementary endpoint -/

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open _root_.CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

private theorem blockShape_heq {n n' r : ℕ} (s : Fin r → ℕ)
    (hp : ∀ i, 0 < s i) (hs : ∑ i, s i = n) (hs' : ∑ i, s i = n') :
    HEq (⟨r, s, hp, hs⟩ : BlockShape n) (⟨r, s, hp, hs'⟩ : BlockShape n') := by
  have h : n = n' := hs.symm.trans hs'
  cases h
  rfl

private theorem induced_rank_congr {n n' : ℕ} (h : n = n')
    {B : BlockShape n} {C : BlockShape n'} (hBC : HEq B C)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (D : letI := T.topology
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (hAD : HEq A D) :
    (h ▸ (T.normalizedProductInductionFunctor B).obj A) =
      (T.normalizedProductInductionFunctor C).obj D := by
  subst n'
  cases hBC
  cases hAD
  rfl

private theorem complementaryInduced_eq_binary (d : SpehDatum.{uF,uV} F T)
    (S : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier)) (α : ℝ)
    (h : d.degree + d.degree = 2 * d.degree) :
    (h ▸ (T.binaryPositiveProductFunctor d.degree_pos d.degree_pos).obj
      (T.segmentFactor S α, T.segmentFactor S (-α))) = d.complementaryInduced S α := by
  let := T.topology
  change (h ▸ (T.normalizedProductInductionFunctor
      (BlockShape.binary d.degree d.degree d.degree_pos d.degree_pos)).obj
      ((T.binaryPairFamilyFunctor d.degree_pos d.degree_pos).obj
        (T.segmentFactor S α, T.segmentFactor S (-α)))) =
    (T.normalizedProductInductionFunctor
      (BlockShape.uniform 2 d.degree d.degree_pos)).obj
      (fun i => T.segmentFactor S (if (i : ℕ) = 0 then α else -α))
  apply induced_rank_congr h
  · unfold BlockShape.binary BlockShape.uniform
    have hs : Fin.cases d.degree (fun _ : Fin 1 => d.degree) =
        (fun _ : Fin 2 => d.degree) := by
      funext i
      fin_cases i <;> rfl
    simp only [hs]
    exact blockShape_heq _ _ _ _
  · apply Function.hfunext rfl
    intro i j hij
    cases hij
    fin_cases i <;> rfl

private theorem head_rank_transport {n n' : ℕ} (h : n = n')
    {a : T.Multisegment.{max uF uV,uF}}
    {P : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hP : a.IsLanglandsHead P) : a.IsLanglandsHead (h ▸ P) := by
  subst n'
  exact hP

private def iso_rank_transport {n n' : ℕ} (h : n = n')
    {P Q : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (e : P ≅ Q) : (h ▸ P) ≅ (h ▸ Q) := by
  subst n'
  exact e

private theorem subquotient_rank_transport_right {n n' : ℕ} (h : n = n')
    {P : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n' F.Carrier)}
    {Q : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hPQ : letI := T.topology; SmoothRep.IsSubquotient (h.symm ▸ P) Q) :
    letI := T.topology
    SmoothRep.IsSubquotient P (h ▸ Q) := by
  subst n'
  exact hPQ

/-- Binary Langlands-head occurrence gives the endpoint constituent after the
two centered parameter sums have been identified. -/
theorem spehNeighborProductEndpointSubquotient_of_headProductSubquotient
    (hA4 : LanglandsHeadProductSubquotient.{uF,uV} F T) :
    SpehNeighborProductEndpointSubquotient.{uF,uV} F T := by
  let := T.topology
  intro d hk hd S Sup Sdown hS hSup hSdown hprod h
  obtain ⟨Δ, hΔ, hδ⟩ :=
    (segmentEssentialSquareIntegrableClassification.{uF,uV} F T
      d.rank d.rank_pos d.delta hd.1).mp hd.2.2.isEssentiallySquareIntegrable
  let dup := d.withLength (d.length + 1) (Nat.succ_pos _)
  let ddown := d.withLength (d.length - 1) (Nat.sub_pos_of_lt hk)
  let a := spehSegmentMultisegment Δ d.length
  let aup := spehSegmentMultisegment Δ dup.length
  let adown := spehSegmentMultisegment Δ ddown.length
  have hSa : a.IsLanglandsHead S :=
    SpehDatum.IsSpeh.isLanglandsHead d Δ hΔ hδ hS
  have hSupA : aup.IsLanglandsHead Sup :=
    SpehDatum.IsSpeh.isLanglandsHead dup Δ hΔ hδ hSup
  have hSdownA : adown.IsLanglandsHead Sdown :=
    SpehDatum.IsSpeh.isLanglandsHead ddown Δ hΔ hδ hSdown
  have hdegree : (aup + adown).degree = dup.degree + ddown.degree := by
    calc
      (aup + adown).degree = aup.degree + adown.degree := by
        simp [Multisegment.degree]
      _ = dup.degree + ddown.degree := by
        simp only [aup, adown, spehSegmentMultisegment_degree, hΔ]
        rfl
  obtain ⟨P₀, hP₀⟩ := multisegmentHeadExistence.{uF,uV} F T (aup + adown)
  let P := hdegree ▸ P₀
  have hP : (aup + adown).IsLanglandsHead P := head_rank_transport hdegree hP₀
  have hPi : P.IsIrreducible := by
    obtain ⟨D, _, _, _, hhead⟩ := hP
    exact hhead.1
  have hPN := hA4 dup.degree ddown.degree dup.degree_pos ddown.degree_pos
    aup adown Sup Sdown P hSupA hSdownA hP
  obtain ⟨e⟩ := CuspidalSupport.NormalHecke.nonempty_iso_of_isSubquotient hprod hPi hPN
  have htwo : d.degree + d.degree = 2 * d.degree := (two_mul d.degree).symm
  let Pfinal := h ▸ P
  let P' := htwo.symm ▸ Pfinal
  have hP' : (aup + adown).IsLanglandsHead P' :=
    head_rank_transport htwo.symm (head_rank_transport h hP)
  have hparameter : a.twist (1 / 2) + a.twist (-(1 / 2)) = aup + adown :=
    spehSegmentMultisegment_endpoint Δ d.length (by omega)
  have hPc : (a.twist (1 / 2) + a.twist (-(1 / 2))).IsLanglandsHead P' := by
    rw [hparameter]
    exact hP'
  have hSpos :=
    (multisegmentConstituentRealTwistCompatibility.{uF,max uF uV} F T
      d.degree d.degree_pos a (1 / 2) S).2.mp hSa
  have hSneg :=
    (multisegmentConstituentRealTwistCompatibility.{uF,max uF uV} F T
      d.degree d.degree_pos a (-(1 / 2)) S).2.mp hSa
  have hPE := hA4 d.degree d.degree d.degree_pos d.degree_pos
    (a.twist (1 / 2)) (a.twist (-(1 / 2)))
    (T.segmentFactor S (1 / 2)) (T.segmentFactor S (-(1 / 2)))
    P' hSpos hSneg hPc
  have hNE := SmoothRep.IsSubquotient.of_iso_left
    (iso_rank_transport htwo.symm (iso_rank_transport h e)) hPE
  have hfinal := subquotient_rank_transport_right (T := T) htwo hNE
  rw [complementaryInduced_eq_binary d S (1 / 2) htwo] at hfinal
  exact hfinal

end Langlands.Classification
