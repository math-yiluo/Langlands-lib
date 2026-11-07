import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof
import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.SegmentConstituentRealTwistCompatibilityProof
import Langlands.Representation.Classification.LinkedSegmentHeadExponentProof
import Langlands.Representation.Classification.SegmentTensorStabilizerProof

/-! # Ordered-head reduction of higher-Speh elimination -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ordered-head parameter uniqueness forces the label of a generic quotient
to be an unlinked multisegment. The uniqueness input remains explicit. -/
theorem genericLanglandsQuotient_isUnlinked
    (hc : OrderedMultisegmentHeadClassification.{uF,uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (d : T.SegmentProductDatum.{max uF uV,uF} (n + 1))
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier))
    (hd : d.IsLanglandsQuotient π)
    (hg : letI := T.topology; Whittaker.IsGeneric ψ n π.representation) :
    d.multisegment.IsUnlinked := by
  let := T.topology
  obtain ⟨e, he, hu, ⟨a⟩⟩ :=
    (genericSegmentProductExhaustion.{uF,uV} T ψ n π).mp hg
  have ho : e.IsPrecedenceOrdered := by
    intro i j _ hp
    exact hu _ (by simp [SegmentProductDatum.multisegment])
      _ (by simp [SegmentProductDatum.multisegment]) hp.isLinked
  have hq : e.IsLanglandsQuotient π := by
    refine ⟨ho, he, hg.1, ?_⟩
    exact ⟨(SmoothRep.equivOfIso a.symm).toIntertwiningMap,
      (SmoothRep.equivOfIso a.symm).surjective⟩
  have hm := (hc (n + 1) d e π π hd hq).mpr ⟨Iso.refl π⟩
  rwa [hm]

/-- Entrywise nondegeneracy suffices, since the quotient is irreducible and
all irreducible smooth representations here are admissible. -/
theorem nondegenerateLanglandsQuotient_isUnlinked
    (hc : OrderedMultisegmentHeadClassification.{uF,uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (hn : 0 < n) (d : T.SegmentProductDatum.{max uF uV,uF} n)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hd : d.IsLanglandsQuotient π)
    (hf : letI := T.topology
      Whittaker.HasFunctional (N := upperUnipotent n F.Carrier)
        (θ := Whittaker.entrywiseCharacter ψ.complex n) π.representation) :
    d.multisegment.IsUnlinked := by
  let := T.topology
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  apply genericLanglandsQuotient_isUnlinked F T hc ψ m d π hd
  refine ⟨hd.2.2.1, (CuspidalSupport.cuspidalEmbedding F T (m + 1) π hd.2.2.1).1, ?_⟩
  rwa [← Whittaker.entrywiseCharacter_eq_standardCharacter]

/-- A segment and its unit forward twist are linked, including length one. -/
theorem segment_isLinked_twist_one (Δ : T.Segment.{uV,uF}) :
    Δ.IsLinked (Δ.twist 1) := by
  have hm (i : ℕ) : (Δ.twist 1).member i = Δ.member (i + 1) := by
    simp only [Segment.member, Segment.twist, CuspidalDatum.twist_twist]
    congr 1
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨i, _, hi⟩ := h (show Δ.member 0 ∈ Δ.support from ⟨0, Δ.length_pos, rfl⟩)
    rw [hm] at hi
    have := segment_member_injective F T Δ hi
    omega
  · intro h
    obtain ⟨i, hi, he⟩ := h
      (show (Δ.twist 1).member (Δ.length - 1) ∈ (Δ.twist 1).support from
        ⟨Δ.length - 1, by exact Nat.sub_lt Δ.length_pos (by decide), rfl⟩)
    rw [hm] at he
    have := segment_member_injective F T Δ he
    omega
  · let U : T.Segment.{uV,uF} := ⟨Δ.base, Δ.length + 1, by omega⟩
    refine ⟨U, ?_⟩
    ext ρ
    constructor
    · rintro ⟨i, hi, rfl⟩
      change i < Δ.length + 1 at hi
      by_cases h : i < Δ.length
      · exact Or.inl ⟨i, h, rfl⟩
      · have he : i = Δ.length := by omega
        subst i
        exact Or.inr ⟨Δ.length - 1, Nat.sub_lt Δ.length_pos (by decide), by
          rw [hm]
          change Δ.member (Δ.length - 1 + 1) = Δ.member Δ.length
          rw [Nat.sub_add_cancel (by have := Δ.length_pos; omega)]⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨i, by change i < Δ.length + 1; omega, rfl⟩
      · refine ⟨i + 1, by change i + 1 < Δ.length + 1; exact Nat.succ_lt_succ hi, ?_⟩
        exact (hm i).symm

/-- The actual centered product of twists of one supplied segment head. -/
def centeredSegmentHeadDatum (Δ : T.Segment.{max uF uV,uF}) (k : ℕ)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) :
    T.SegmentProductDatum.{max uF uV,uF} (k * Δ.degree) where
  length := k
  segments i := Δ.twist (((k : ℝ) - 1) / 2 - (i : ℕ))
  degree_sum := by simp [Segment.degree]
  blocks i := T.segmentFactor δ (((k : ℝ) - 1) / 2 - (i : ℕ))

theorem centeredSegmentHeadDatum_induced (Δ : T.Segment.{max uF uV,uF}) (k : ℕ)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)) :
    (centeredSegmentHeadDatum F T Δ k δ).induced =
      T.twistedProductInduced (BlockShape.uniform k Δ.degree Δ.degree_pos)
        (fun _ => δ) (fun i => ((k : ℝ) - 1) / 2 - (i : ℕ)) := rfl

theorem centeredSegmentHeadDatum_hasSegmentHeads
    (Δ : T.Segment.{max uF uV,uF}) (k : ℕ)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hh : T.IsSegmentHead Δ δ) :
    (centeredSegmentHeadDatum F T Δ k δ).HasSegmentHeads := by
  intro i
  exact ((segmentConstituentRealTwistCompatibility F T Δ
    (((k : ℝ) - 1) / 2 - (i : ℕ)) δ).2.1).mp hh

theorem centeredSegmentHeadDatum_isPrecedenceOrdered
    (Δ : T.Segment.{max uF uV,uF}) (k : ℕ)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hh : T.IsSegmentHead Δ δ)
    (hu : letI := T.topology; IsUnitarizable δ.representation) :
    (centeredSegmentHeadDatum F T Δ k δ).IsPrecedenceOrdered := by
  let := T.topology
  obtain ⟨form⟩ := hu
  let u : UnitaryExponentData (T.determinantNorm Δ.degree) δ.representation :=
    ⟨0, by simpa using form⟩
  have hheads := centeredSegmentHeadDatum_hasSegmentHeads F T Δ k δ hh
  intro i j hij hp
  have he := ((linkedSegmentHeadExponentComparison F T)
    _ _ _ _ (hheads i) (hheads j)
      (u.shift (((k : ℝ) - 1) / 2 - (i : ℕ)))
      (u.shift (((k : ℝ) - 1) / 2 - (j : ℕ)))).2 hp
  change 0 + (((k : ℝ) - 1) / 2 - (i : ℕ)) <
    0 + (((k : ℝ) - 1) / 2 - (j : ℕ)) at he
  have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
  linarith

theorem centeredSegmentHeadDatum_not_isUnlinked
    (Δ : T.Segment.{max uF uV,uF}) (k : ℕ)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hk : 1 < k) :
    ¬ (centeredSegmentHeadDatum F T Δ k δ).multisegment.IsUnlinked := by
  let a := centeredSegmentHeadDatum F T Δ k δ
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, hk⟩
  have hlinked : (a.segments j).IsLinked (a.segments i) := by
    have h := segment_isLinked_twist_one F T (a.segments j)
    have he : (a.segments j).twist 1 = a.segments i := by
      simp only [a, centeredSegmentHeadDatum, i, j, Nat.cast_one, Nat.cast_zero]
      rw [Segment.twist_twist]
      congr 1
      ring
    rwa [he] at h
  intro h
  exact h _ (by simp [a, SegmentProductDatum.multisegment])
    _ (by simp [a, SegmentProductDatum.multisegment]) hlinked

/-- A nondegenerate irreducible quotient of centered twists of a unitarizable
segment head has exactly one row, assuming ordered-head classification. -/
theorem centeredSegmentHeadQuotient_length_eq_one
    (hc : OrderedMultisegmentHeadClassification.{uF,uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (Δ : T.Segment.{max uF uV,uF}) (k : ℕ) (hk : 0 < k)
    (δ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hh : T.IsSegmentHead Δ δ)
    (hu : letI := T.topology; IsUnitarizable δ.representation)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (k * Δ.degree) F.Carrier))
    (hq : letI := T.topology
      IsIrreducibleQuotient
        (T.twistedProductInduced (BlockShape.uniform k Δ.degree Δ.degree_pos)
          (fun _ => δ) (fun i => ((k : ℝ) - 1) / 2 - (i : ℕ))).representation
        π.representation)
    (hf : letI := T.topology
      Whittaker.HasFunctional (N := upperUnipotent (k * Δ.degree) F.Carrier)
        (θ := Whittaker.entrywiseCharacter ψ.complex (k * Δ.degree)) π.representation) :
    k = 1 := by
  let a := centeredSegmentHeadDatum F T Δ k δ
  have ha : a.IsLanglandsQuotient π :=
    ⟨centeredSegmentHeadDatum_isPrecedenceOrdered F T Δ k δ hh hu,
      centeredSegmentHeadDatum_hasSegmentHeads F T Δ k δ hh, hq⟩
  have h := nondegenerateLanglandsQuotient_isUnlinked F T hc ψ
    (k * Δ.degree) (Nat.mul_pos hk Δ.degree_pos) a π ha hf
  have hle : k ≤ 1 := by
    by_contra hlt
    exact centeredSegmentHeadDatum_not_isUnlinked F T Δ k δ (by omega) h
  omega

/-- Ordered-head classification implies the all-rank higher-Speh exclusion
needed by the unitary generic exhaustion argument. -/
theorem SpehDatum.length_eq_one_of_hasFunctional
    (hc : OrderedMultisegmentHeadClassification.{uF,uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (d : SpehDatum.{uF,uV} F T)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
    (hs : d.IsSpeh π)
    (hf : letI := T.topology
      Whittaker.HasFunctional (N := upperUnipotent d.degree F.Carrier)
        (θ := Whittaker.entrywiseCharacter ψ.complex d.degree) π.representation) :
    d.length = 1 := by
  let := T.topology
  rcases d with ⟨r, hr, k, hk, δ⟩
  rcases hs with ⟨⟨hirr, huni, hsq⟩, hquot, _⟩
  obtain ⟨Δ, he, hhead⟩ :=
    (segmentEssentialSquareIntegrableClassification F T r hr δ hirr).mp
      hsq.isEssentiallySquareIntegrable
  cases he
  exact centeredSegmentHeadQuotient_length_eq_one F T hc ψ Δ k hk δ
    hhead huni π hquot hf

end Langlands.Classification
