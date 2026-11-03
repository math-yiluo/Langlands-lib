import Langlands.Representation.Classification.SegmentSocleCriterionHalvesStatement
import Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStepsStatement
import Langlands.Representation.Classification.SegmentSocleDerivativesStatement
import Langlands.Representation.Classification.SegmentConstituentStatement
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SegmentPrecedenceTruncation
import Langlands.Representation.Classification.SegmentSocleProductComparison
import Langlands.Representation.Filtration.FunctorLengthTwoDetection
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement

/-! Ze80 Proposition 4.6 from its inputs: the juxtaposed case, the nonzero map to
the product of union and intersection, and the derivative statements. -/

namespace Langlands.Classification

open CategoryTheory PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A property of the ordered pairs of distinct segments of a datum of length two
follows from the two orders. -/
theorem forall_ne_of_length_eq_two {n : ℕ} (d : SegmentProductDatum.{uV, uF} T n)
    (h₂ : d.length = 2) (P : Segment.{uV, uF} T → Segment.{uV, uF} T → Prop)
    (h01 : P (d.segments ⟨0, by omega⟩) (d.segments ⟨1, by omega⟩))
    (h10 : P (d.segments ⟨1, by omega⟩) (d.segments ⟨0, by omega⟩)) :
    ∀ i j, i ≠ j → P (d.segments i) (d.segments j) := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  have hne : i ≠ j := fun h => hij (Fin.ext h)
  rcases (by omega : i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h01
  · exact h10

theorem dropLastList_singleton (J : Segment.{uV, uF} T) :
    Segment.dropLastList [J] = J.dropLast.toList := by
  cases h : J.dropLast <;> simp [Segment.dropLastList, h]

/-- Products of segment socles of positive degree with pairwise nonlinked segments
are irreducible. -/
theorem isIrreducible_of_isUnlinked
    (hirr : UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T) {n : ℕ}
    (e : SegmentProductDatum.{uV, uF} T n) (hn : 0 < n) (hes : e.HasSegmentSocles)
    (hu : e.multisegment.IsUnlinked) :
    letI := T.topology
    Representation.IsIrreducible e.induced.representation := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hirr m e hes hu

/-- Ze80 Proposition 4.6 from the juxtaposed case (A), the nonzero map (B), the
existence of segment socles, the irreducibility of unlinked products, the lattice
form (e) of Ze80 4.3, the highest derivative (f) of a product of segment socles, and
the existence of a nontrivial unitary additive character. -/
theorem linkedSegmentSocleReverseProductStructure_of
    (hψ : HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement.{uF} F T)
    (hex : SegmentZelevinskyConstituentExistence.{uF, uV} F T)
    (hirr : UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T)
    (hA : JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T)
    (hB : LinkedSegmentSocleReverseProductQuotientHom.{uF, uV} F T)
    (he : NonjuxtaposedSegmentSocleDerivativeStrictMono.{uF, uV} F T)
    (hf : SegmentSocleProductHighestDerivative.{uF, uV} F T) :
    LinkedSegmentSocleReverseProductStructure.{uF, uV} F T := by
  let _ := T.topology
  have hfree := cuspidalIntegralTwistFreeness.{uF, uV} F T
  obtain ⟨ψ⟩ := hψ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d h₂ hs hp
  by_cases hj : (d.segments ⟨1, by omega⟩).IsJuxtaposed (d.segments ⟨0, by omega⟩)
  · exact hA n d h₂ hs hp hj
  obtain ⟨hAl, hBl, U, J, hU, hrepl, hp', hrepl', hBr, hUr, hJr, hJU⟩ :=
    Segment.Precedes.truncation hfree hp hj
  -- The segments of `d` and the degree `n`.
  have hdseg : List.ofFn d.segments = [d.segments ⟨0, by omega⟩, d.segments ⟨1, by omega⟩] :=
    (SegmentProductDatum.ofFn_segments_eq_pair d h₂ _ _).2 ⟨rfl, rfl⟩
  have hn : (d.segments ⟨0, by omega⟩).degree + (d.segments ⟨1, by omega⟩).degree = n := by
    have := SegmentProductDatum.sum_map_degree_ofFn d
    rw [hdseg] at this
    simpa using this
  have hUJ : U.degree + J.degree =
      (d.segments ⟨1, by omega⟩).degree + (d.segments ⟨0, by omega⟩).degree := by
    simpa using hrepl.symm.degree_sum hfree hp
  -- The product `ω = ⟨U⟩ × ⟨J⟩`.
  have hlist : ([U, J].map Segment.degree).sum = n := by simp; omega
  let e := SegmentProductDatum.ofSegmentList [U, J] hlist
  have heseg : List.ofFn e.segments = U :: (some J).toList :=
    SegmentProductDatum.ofFn_segments_ofSegmentList _ _
  have hes : e.HasSegmentSocles :=
    SegmentProductDatum.hasSegmentSocles_ofSegmentList hex _ _
  have hunl : e.multisegment.IsUnlinked := by
    intro Δ₁ h₁ Δ₂ h₂' hl
    change Δ₁ ∈ ((List.ofFn e.segments : List _) : Multiset _) at h₁
    change Δ₂ ∈ ((List.ofFn e.segments : List _) : Multiset _) at h₂'
    rw [heseg] at h₁ h₂'
    simp only [Option.toList_some, Multiset.mem_coe, List.mem_cons,
      List.not_mem_nil, or_false] at h₁ h₂'
    rcases h₁ with rfl | rfl <;> rcases h₂' with rfl | rfl
    · exact hl.1 subset_rfl
    · exact hl.2.1 hJU
    · exact hl.1 hJU
    · exact hl.1 subset_rfl
  have heirr : Representation.IsIrreducible e.induced.representation :=
    isIrreducible_of_isUnlinked hirr e (by have := (d.segments ⟨0, by omega⟩).degree_pos; omega)
      hes hunl
  -- Step (2): a nonzero map `⟨Δ⟩ × ⟨Δ'⟩ → ω`.
  obtain ⟨f, hf0⟩ := hB n d h₂ hs hp U (some J) e hrepl heseg hes
  -- The order `λ` of the highest derivative.
  have hk_eq : ∑ i, (d.segments i).rank =
      (d.segments ⟨0, by omega⟩).rank + (d.segments ⟨1, by omega⟩).rank := by
    rw [SegmentProductDatum.sum_rank_eq, hdseg]
    simp
  have hk : ∑ i, (d.segments i).rank ≤ n := by
    rw [hk_eq]
    have h0 := Nat.le_mul_of_pos_left (d.segments ⟨0, by omega⟩).rank
      (d.segments ⟨0, by omega⟩).length_pos
    have h1 := Nat.le_mul_of_pos_left (d.segments ⟨1, by omega⟩).rank
      (d.segments ⟨1, by omega⟩).length_pos
    simp only [Segment.degree] at hn
    omega
  have hkpos : 0 < ∑ i, (d.segments i).rank := by
    rw [hk_eq]
    have := (d.segments ⟨0, by omega⟩).rank_pos
    omega
  have hke : ∑ i, (d.segments i).rank = ∑ i, (e.segments i).rank := by
    rw [hk_eq, SegmentProductDatum.sum_rank_eq e, heseg]
    simp
    omega
  -- Strict monotonicity of the derivative on subrepresentations of `⟨Δ⟩ × ⟨Δ'⟩`.
  have hmono := he ψ n d hs
    (forall_ne_of_length_eq_two d h₂ (fun x y => ¬ x.IsJuxtaposed y)
      (fun h => hj ((Segment.isJuxtaposed_comm _ _).1 h)) hj)
    _ hk rfl
  -- The highest derivative of `⟨Δ⟩ × ⟨Δ'⟩` is `⟨Δ⁻⟩ × ⟨Δ'⁻⟩`.
  obtain ⟨-, ⟨d', hd'seg, hd's, ⟨φ⟩⟩, -⟩ := hf ψ n d hs _ hk rfl
  rw [Segment.filterMap_eq_dropLastList, hdseg] at hd'seg
  simp only [Segment.dropLastList_cons_of_one_lt _ hBl, Segment.dropLastList_cons_of_one_lt _ hAl,
    Segment.dropLastList_nil] at hd'seg
  have h₂' : d'.length = 2 := by simpa using congrArg List.length hd'seg
  obtain ⟨hd'0, hd'1⟩ := (SegmentProductDatum.ofFn_segments_eq_pair d' h₂' _ _).1 hd'seg
  -- The induction hypothesis for `⟨Δ⁻⟩ × ⟨Δ'⁻⟩`.
  obtain ⟨U', I', e', hrepl'', he'seg, he's, he'irr, s', hs', -, hgr0, huniq'⟩ :=
    ih _ (by omega) d' h₂' hd's (by rw [hd'0, hd'1]; exact hp')
  rw [hd'0, hd'1] at hrepl''
  obtain ⟨rfl, rfl⟩ := hrepl''.unique hfree hrepl'
  -- The highest derivative of `ω` is `⟨U⁻⟩ × ⟨J⁻⟩`.
  obtain ⟨-, ⟨e'', he''seg, he''s, ⟨θ₀⟩⟩, -⟩ := hf ψ n e hes _ hk hke
  rw [Segment.filterMap_eq_dropLastList, heseg] at he''seg
  simp only [Option.toList_some, Segment.dropLastList_cons_of_one_lt _ hU] at he''seg
  rw [← dropLastList_singleton] at he'seg
  obtain ⟨c⟩ := SegmentProductDatum.nonempty_iso_of_ofFn_segments_eq
    (he''seg.trans he'seg.symm) he''s he's
  -- Step (3): length two through the derivative.
  let θ := SmoothRep.equivOfIso (θ₀ ≪≫ c)
  obtain ⟨S, hS0, hS2, hS, hSne⟩ := FunctorLengthTwo.exists_middle_of_equiv
    (SmoothRep.equivOfIso φ) s' hs' huniq' θ hgr0
  have hDY := LengthTwo.isIrreducible_of_equiv θ.symm he'irr
  exact ⟨U, some J, e, hrepl, heseg, hes, heirr,
    FunctorLengthTwo.lengthTwo_of_strictMono _ d.induced e.induced f hf0 heirr hmono S hS0
      hS2 hS hDY hSne⟩

end Langlands.Classification
