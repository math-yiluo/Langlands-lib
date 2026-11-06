import Langlands.Representation.Classification.SegmentGenericStatement
import Langlands.Representation.Classification.SegmentHeadReplacementDatum
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.Representation.Classification.SegmentHeadProductCuspidalSupportProof
import Langlands.Representation.Classification.SegmentHeadProductIrreducibilityProof
import Langlands.Representation.Classification.SegmentHeadProductTopDerivative
import Langlands.Representation.CuspidalSupport.FixedSupportDetectedEquiv
import Langlands.Representation.Derivative.TopLocalizationComparison
import Langlands.Representation.Whittaker.LocalizationDual
import Langlands.Representation.Whittaker.Transport

/-! Generic representations as unlinked products of actual special heads. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Multisegment

private def squareWeight (a : Multisegment.{uV,uF} T) : ℕ :=
  (a.map fun Δ => Δ.length ^ 2).sum

private theorem content_card (a : Multisegment.{uV,uF} T) :
    a.cuspidalContent.card = (a.map Segment.length).sum := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons Δ a ih => simp [ih]

private theorem squareWeight_le (a : Multisegment.{uV,uF} T) :
    squareWeight a ≤ a.cuspidalContent.card ^ 2 := by
  induction a using Multiset.induction_on with
  | empty => simp [squareWeight]
  | cons Δ a ih =>
    simp only [squareWeight, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
    rw [cuspidalContent_cons, Multiset.card_add, Segment.card_cuspidalContent]
    nlinarith [Nat.zero_le (Δ.length * (cuspidalContent a).card)]

private theorem square_sum_lt {a b c d : ℕ} (ha : a < c) (hb : b < c)
    (hs : c + d = a + b) : a ^ 2 + b ^ 2 < c ^ 2 + d ^ 2 := by
  have ha' : (0 : ℤ) < (c : ℤ) - a := by omega
  have hb' : (0 : ℤ) < (c : ℤ) - b := by omega
  have hp := mul_pos ha' hb'
  zify at hs ⊢
  nlinarith

private theorem replacement_squareWeight_lt
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF,uV} F T)
    {Δ Γ U : Segment.{uV,uF} T} {I : Option (Segment.{uV,uF} T)}
    (hp : Δ.Precedes Γ) (hs : Segment.IsUnionIntersectionReplacement Δ Γ U I) :
    Δ.length ^ 2 + Γ.length ^ 2 <
      U.length ^ 2 + (I.toList.map fun J => J.length ^ 2).sum := by
  obtain ⟨ρ, a, b, c, d, hΔ, hΓ, hends, hU, _⟩ := hs.coordinates hfree hp
  have hΔlen := hΔ.2
  have hΓlen := hΓ.2
  have hUlen := hU.2
  have hlargeΔ : Δ.length < U.length := by obtain ⟨_, _, _⟩ := hends; omega
  have hlargeΓ : Γ.length < U.length := by obtain ⟨_, _, _⟩ := hends; omega
  have hsum := hs.length_sum hfree hp
  cases I with
  | none =>
    simp only [Option.toList_none, List.map_nil, List.sum_nil, add_zero] at hsum ⊢
    simpa using square_sum_lt hlargeΔ hlargeΓ (d := 0) (by omega)
  | some J =>
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero] at hsum ⊢
    exact square_sum_lt hlargeΔ hlargeΓ hsum

private theorem singleton_content (S : Multiset (CuspidalDatum.{uV,uF} T)) :
    cuspidalContent (S.map fun ρ => (⟨ρ, 1, Nat.one_pos⟩ : Segment.{uV,uF} T)) = S := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons ρ S ih => simp [ih]

/-- Every finite multiset of cuspidal data is the content of an unlinked
multisegment, retaining all occurrences. -/
theorem exists_unlinked_of_cuspidalContent
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF,uV} F T)
    (S : Multiset (CuspidalDatum.{uV,uF} T)) :
    ∃ a : Multisegment.{uV,uF} T, a.IsUnlinked ∧ a.cuspidalContent = S := by
  classical
  have hex : ∃ k : ℕ, ∃ a : Multisegment.{uV,uF} T,
      a.cuspidalContent = S ∧ S.card ^ 2 - squareWeight a = k :=
    ⟨_, S.map (fun ρ => ⟨ρ, 1, Nat.one_pos⟩), singleton_content S, rfl⟩
  obtain ⟨a, ha, hcost⟩ := Nat.find_spec hex
  refine ⟨a, ?_, ha⟩
  intro Δ hΔ Γ hΓ hlink
  have hne : Δ ≠ Γ := by rintro rfl; exact Segment.not_isLinked_self _ hlink
  have hΓ' : Γ ∈ a.erase Δ := Multiset.mem_erase_of_ne hne.symm |>.mpr hΓ
  let rest := (a.erase Δ).erase Γ
  have heq : a = Δ ::ₘ Γ ::ₘ rest := by
    calc
      a = Δ ::ₘ a.erase Δ := (Multiset.cons_erase hΔ).symm
      _ = Δ ::ₘ Γ ::ₘ rest :=
        congrArg (Multiset.cons Δ) (Multiset.cons_erase hΓ').symm
  rcases hlink.precedes_or_precedes with hp | hp
  all_goals
    obtain ⟨U, I, hs⟩ := Segment.exists_unionIntersectionReplacement hfree hp
    let b : Multisegment.{uV,uF} T := U ::ₘ (I.toList : Multiset _) + rest
    have hb : b.cuspidalContent = S := by
      have he := hs.cuspidalContent_sum hfree
      change cuspidalContent ((U ::ₘ (I.toList : Multiset _)) + rest) = S
      rw [cuspidalContent_add, cuspidalContent_cons]
      have hI : cuspidalContent (I.toList : Multiset _) =
          (I.toList.map Segment.cuspidalContent).sum := by
        simp [cuspidalContent]
      rw [hI, he]
      have ha' := ha
      rw [heq] at ha'
      simpa [add_assoc, add_comm, add_left_comm] using ha'
    have hw : squareWeight a < squareWeight b := by
      have hlt := replacement_squareWeight_lt hfree hp hs
      change squareWeight a < squareWeight ((U ::ₘ (I.toList : Multiset _)) + rest)
      rw [heq]
      simp only [squareWeight, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_add, Multiset.sum_add, Multiset.map_coe, Multiset.sum_coe]
      omega
    have hbound := squareWeight_le b
    rw [hb] at hbound
    have hminimal := Nat.find_min' hex ⟨b, hb, rfl⟩
    omega

end Multisegment

end Langlands.PadicField.TopologicalData

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

private def rankCastLinearEquiv {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    X ≃ₗ[ℂ] (generalLinearRankCast T h).obj X := by
  subst b
  exact LinearEquiv.refl ℂ X

private theorem functional_iff_top_nontrivial
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (π : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    letI := T.topology
    Whittaker.HasFunctional
      (N := upperUnipotent (n + 1) F.Carrier)
      (θ := Whittaker.standardCharacter ψ n) π.representation ↔
      Nontrivial ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π) := by
  let := T.topology
  let U := upperUnipotent (n + 1) F.Carrier
  let θ := Whittaker.entrywiseCharacter ψ.complex (n + 1)
  let Q := Jacquet.Localization.Coinvariants π.representation U θ
  let f := Whittaker.functionalsLocalizationDualEquiv U θ π.representation
  let e := (SmoothRep.equivOfIso
    ((TopLocalization.topLocalizationIso T ψ (n + 1)).app π)).toLinearEquiv
  let r := rankCastLinearEquiv T (Nat.sub_self (n + 1))
    ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π)
  have hf : Whittaker.HasFunctional (N := U) (θ := θ) π.representation ↔
      Nontrivial (Whittaker.functionals U θ π.representation) := by
    constructor
    · rintro ⟨ℓ, hℓ⟩
      exact nontrivial_of_ne ℓ 0 (fun h => hℓ (congrArg Subtype.val h))
    · intro h
      let := h
      obtain ⟨ℓ, hℓ⟩ := exists_ne (0 : Whittaker.functionals U θ π.representation)
      exact ⟨ℓ, fun hzero => hℓ (Subtype.ext hzero)⟩
  rw [← Whittaker.entrywiseCharacter_eq_standardCharacter]
  change Whittaker.HasFunctional (N := U) (θ := θ) π.representation ↔ _
  exact hf.trans ((Equiv.nontrivial_congr f.toEquiv).trans
    ((Module.nontrivial_dual_iff ℂ).trans
      ((Equiv.nontrivial_congr e.toEquiv).trans
        (Equiv.nontrivial_congr r.toEquiv).symm)))

/-- A generic smooth representation is an actual whole product of special
segment heads for a pairwise unlinked multisegment, and conversely. -/
theorem genericSegmentProductExhaustion :
    GenericSegmentProductExhaustion.{uF,uV} F T := by
  classical
  let := T.topology
  intro ψ n π
  constructor
  · intro hπ
    obtain ⟨k, ρ, hρ⟩ :=
      glSupercuspidalEmbedding.{max uF uV,uF} p F T (n + 1) (Nat.succ_pos n) π hπ.1
    let S : Multiset (CuspidalDatum.{max uF uV,uF} T) := List.ofFn ρ
    have hS : T.IsSupercuspidalSupport π S := ⟨k, ρ, rfl, hρ.isCuspidalConstituent⟩
    obtain ⟨a, ha, hcontent⟩ := Multisegment.exists_unlinked_of_cuspidalContent
      (cuspidalIntegralTwistFreeness F T) S
    have hdegree : a.degree = n + 1 := by
      rw [← Multisegment.sum_rank_cuspidalContent, hcontent]
      exact hS.sum_rank
    have hlist : (a.toList.map Segment.degree).sum = n + 1 := by
      calc
        _ = ((↑a.toList : Multiset (Segment.{max uF uV,uF} T)).map
            Segment.degree).sum := by
          simp only [Multiset.map_coe, Multiset.sum_coe]
        _ = a.degree := by rw [Multiset.coe_toList]; rfl
        _ = n + 1 := hdegree
    obtain ⟨d, hd, hsegments⟩ := segmentHeadDatumOfList.{uF,max uF uV} T a.toList hlist
    have hmult : d.multisegment = a := by
      change (List.ofFn d.segments : Multiset _) = a
      rw [hsegments, Multiset.coe_toList]
    have hunlinked : d.multisegment.IsUnlinked := hmult.symm ▸ ha
    have hirr : d.induced.IsIrreducible :=
      (segmentHeadProductIrreducibility.{uF,max uF uV} F T n d hd).mpr hunlinked
    have hsupport : T.IsSupercuspidalSupport d.induced S := by
      have h := segmentHeadProductCuspidalSupport.{uF,uV} F T (n + 1) d hd hirr
      rwa [hmult, hcontent] at h
    let e := CuspidalSupport.fixedSupportDetectedEquiv.{uF,max uF uV} T ψ (Nat.succ_pos n)
      π d.induced S hS hsupport
      ((functional_iff_top_nontrivial T ψ n π).mp hπ.2.2)
      (segmentHeadProductTopDerivativeNontrivial.{uF,max uF uV} T ψ (Nat.succ_pos n) d hd)
    exact ⟨d, hd, hunlinked, ⟨SmoothRep.mkIso e⟩⟩
  · rintro ⟨d, hd, hu, ⟨e⟩⟩
    have hirr : d.induced.IsIrreducible :=
      (segmentHeadProductIrreducibility.{uF,max uF uV} F T n d hd).mpr hu
    have hadm := (CuspidalSupport.cuspidalEmbedding F T (n + 1) d.induced hirr).1
    have hfunctional := (functional_iff_top_nontrivial T ψ n d.induced).mpr
      (segmentHeadProductTopDerivativeNontrivial T ψ (Nat.succ_pos n) d hd)
    exact (Whittaker.isGeneric_iff_of_equiv ψ n (SmoothRep.equivOfIso e)).mpr
      ⟨hirr, hadm, hfunctional⟩

end Langlands.Classification
