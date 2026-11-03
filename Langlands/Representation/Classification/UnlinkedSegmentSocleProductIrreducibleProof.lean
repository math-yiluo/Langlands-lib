import Langlands.Representation.Classification.SegmentSocleCriterionHalvesStatement
import Langlands.Representation.Classification.SegmentSocleDerivativesStatement
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.Representation.Classification.SegmentSocleProductHighestDerivativeProof
import Langlands.Representation.Classification.NonjuxtaposedSegmentSocleDerivativeStrictMonoProof
import Langlands.Representation.Classification.SegmentIntervalLinkage
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.RegularLanglandsHeadReduction
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-!
# Products of unlinked segment socles are irreducible

Zelevinsky (1980), Theorem 4.2, implication (2)⇒(1), following §4.3: induction
on the degree through the highest derivative of the product.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

namespace UnlinkedSegmentSocleProductIrreducibleProof

section Combinatorics

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

open PadicField.TopologicalData.Segment in
/-- If `Δ⁻` precedes `Γ⁻`, then `Δ` precedes `Γ`. -/
theorem precedes_of_minus_precedes {Δ Γ : T.Segment.{uV, uF}}
    (hΔ : 2 ≤ Δ.length) (hΓ : 2 ≤ Γ.length)
    (h : (⟨Δ.base, Δ.length - 1, by omega⟩ : T.Segment.{uV, uF}).Precedes
      ⟨Γ.base, Γ.length - 1, by omega⟩) :
    Δ.Precedes Γ := by
  have hfree := cuspidalIntegralTwistFreeness.{uF, uV} F T
  have hΔ' : (⟨Δ.base, Δ.length - 1, by omega⟩ : T.Segment.{uV, uF}).HasIntegralCoordinates
      Δ.base 0 ((Δ.length : ℤ) - 2) := by
    refine ⟨by simp, ?_⟩
    change (Δ.length : ℤ) - 2 = 0 + ((Δ.length - 1 : ℕ) : ℤ) - 1
    omega
  obtain ⟨c, e, hΓ'⟩ := hΔ'.of_precedes_right h
  obtain ⟨h1, h2, h3⟩ := (hΔ'.precedes_iff hfree hΓ').mp h
  have hΔc := Δ.hasIntegralCoordinates_self
  have hΓc : Γ.HasIntegralCoordinates Δ.base c (e + 1) := by
    refine ⟨hΓ'.1, ?_⟩
    have := hΓ'.2
    change e = c + ((Γ.length - 1 : ℕ) : ℤ) - 1 at this
    omega
  exact (hΔc.precedes_iff hfree hΓc).mpr ⟨h1, by omega, by omega⟩

/-- Ze80 4.1: if `Δ⁻` and `Γ⁻` are linked, so are `Δ` and `Γ`. -/
theorem isLinked_of_minus_isLinked {Δ Γ : T.Segment.{uV, uF}}
    (hΔ : 2 ≤ Δ.length) (hΓ : 2 ≤ Γ.length)
    (h : (⟨Δ.base, Δ.length - 1, by omega⟩ : T.Segment.{uV, uF}).IsLinked
      ⟨Γ.base, Γ.length - 1, by omega⟩) :
    Δ.IsLinked Γ := by
  rcases h.precedes_or_precedes with h | h
  · exact (precedes_of_minus_precedes hΔ hΓ h).isLinked
  · exact (precedes_of_minus_precedes hΓ hΔ h).isLinked.symm

/-- Dropping the ends of an unlinked family, and omitting singletons, keeps it
unlinked. -/
theorem isUnlinked_of_filterMap_minus {n m : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (d' : T.SegmentProductDatum.{uV, uF} m)
    (hd' : List.ofFn d'.segments =
      (List.ofFn d.segments).filterMap (fun Δ =>
        if h : 2 ≤ Δ.length then
          some (⟨Δ.base, Δ.length - 1, by omega⟩ : T.Segment.{uV, uF})
        else none))
    (hu : d.multisegment.IsUnlinked) : d'.multisegment.IsUnlinked := by
  intro Γ₁ hΓ₁ Γ₂ hΓ₂ hl
  simp only [PadicField.TopologicalData.SegmentProductDatum.multisegment, Multiset.mem_coe,
    hd', List.mem_filterMap] at hΓ₁ hΓ₂
  obtain ⟨Δ₁, hΔ₁, h₁⟩ := hΓ₁
  obtain ⟨Δ₂, hΔ₂, h₂⟩ := hΓ₂
  split_ifs at h₁ with hl₁
  split_ifs at h₂ with hl₂
  cases h₁
  cases h₂
  exact hu Δ₁ (Multiset.mem_coe.mpr hΔ₁) Δ₂ (Multiset.mem_coe.mpr hΔ₂)
    (isLinked_of_minus_isLinked hl₁ hl₂ hl)

end Combinatorics

section Lattice

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A nonzero representation has two distinct subrepresentations. -/
theorem subrepresentation_nontrivial (ρ : Representation ℂ G V) [Nontrivial V] :
    Nontrivial (Subrepresentation ρ) :=
  ⟨⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤)
    (congrArg Subrepresentation.toSubmodule h)⟩⟩

/-- A one-dimensional representation is irreducible. -/
theorem isIrreducible_of_finrank_eq_one (ρ : Representation ℂ G V)
    (h : Module.finrank ℂ V = 1) : Representation.IsIrreducible ρ := by
  have : Module.Finite ℂ V := Module.finite_of_finrank_eq_succ h
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
  refine { toNontrivial := subrepresentation_nontrivial ρ, eq_bot_or_eq_top := fun K => ?_ }
  have hle : Module.finrank ℂ K.toSubmodule ≤ 1 := h ▸ Submodule.finrank_le _
  interval_cases hK : Module.finrank ℂ K.toSubmodule
  · left
    exact Subrepresentation.toSubmodule_injective (Submodule.finrank_eq_zero.mp hK)
  · right
    exact Subrepresentation.toSubmodule_injective
      (Submodule.eq_top_of_finrank_eq (hK.trans h.symm))

end Lattice

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A datum of positive degree has at least one segment. -/
theorem length_pos_of_degree {N : ℕ} (d : T.SegmentProductDatum.{uV, uF} N) (hN : 0 < N) :
    0 < d.length := by
  rcases Nat.eq_zero_or_pos d.length with h | h
  · exfalso
    have hsum := d.degree_sum
    have : IsEmpty (Fin d.length) := by rw [h]; exact Fin.isEmpty'
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    omega
  · exact h

/-- Ze80 §4.3: the target follows from the existence of `ψ`, the lattice form (e)
of Ze80 Proposition 4.3 and the highest derivative (f) of a product of segment
socles. -/
theorem of_derivatives
    (hψ : HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement F T)
    (he : NonjuxtaposedSegmentSocleDerivativeStrictMono.{uF, uV} F T)
    (hf : SegmentSocleProductHighestDerivative.{uF, uV} F T) :
    UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T := by
  let := T.topology
  obtain ⟨ψ⟩ := hψ
  suffices H : ∀ (N : ℕ) (d : T.SegmentProductDatum.{uV, uF} N), 0 < d.length →
      d.HasSegmentSocles → d.multisegment.IsUnlinked →
        Representation.IsIrreducible d.induced.representation by
    intro n d hs hu
    exact H (n + 1) d (length_pos_of_degree F T d (Nat.succ_pos n)) hs hu
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro d hlen hs hu
  -- the order `λ = ∑ i, rank Δ_i` of the highest derivative
  have hkN : ∑ i, (d.segments i).rank ≤ N :=
    calc ∑ i, (d.segments i).rank ≤ ∑ i, (d.segments i).degree :=
          Finset.sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (d.segments i).length_pos
      _ = N := d.degree_sum
  have hkpos : 0 < ∑ i, (d.segments i).rank :=
    Finset.sum_pos (fun i _ => (d.segments i).rank_pos) ⟨⟨0, hlen⟩, Finset.mem_univ _⟩
  obtain ⟨-, ⟨d', hd', hs', ⟨iso⟩⟩, hone⟩ := hf ψ N d hs _ hkN rfl
  -- the highest derivative is irreducible
  have hX : Representation.IsIrreducible
      ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ N
        (∑ i, (d.segments i).rank) hkN).obj d.induced).representation := by
    by_cases hall : ∀ i, (d.segments i).length = 1
    · exact isIrreducible_of_finrank_eq_one _ (hone hall)
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have h2 : 2 ≤ (d.segments i).length := by
        have := (d.segments i).length_pos
        omega
      have hmem : (⟨(d.segments i).base, (d.segments i).length - 1, by omega⟩ :
          T.Segment.{uV, uF}) ∈ List.ofFn d'.segments := by
        rw [hd', List.mem_filterMap]
        exact ⟨d.segments i, List.mem_ofFn.mpr ⟨i, rfl⟩, by simp [h2]⟩
      have hlen' : 0 < d'.length := by
        have hne := List.ne_nil_of_mem hmem
        rw [Ne, List.ofFn_eq_nil_iff] at hne
        omega
      have hirr := ih _ (by omega) d' hlen' hs' (isUnlinked_of_filterMap_minus d d' hd' hu)
      exact (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso iso)).mpr hirr
  -- the product is nonzero
  have hblocks : ∀ i, Nontrivial (d.blocks i) := fun i => by
    obtain ⟨A, -, hsoc⟩ := hs i
    exact Langlands.CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible
      _ hsoc.1
  have : Nontrivial d.induced :=
    RegularHeadExistence.nontrivial_normalizedProductInduction T d.shape d.blocks hblocks
  -- unlinked segments are pairwise not juxtaposed
  have hnj : ∀ i j, i ≠ j → ¬ (d.segments i).IsJuxtaposed (d.segments j) := by
    intro i j _ hij
    exact hu _ (Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)) _
      (Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩)) hij.1
  -- a proper nonzero subrepresentation `K` would give `⊥ < D(K) < ⊤` inside the
  -- irreducible highest derivative
  refine { toNontrivial := subrepresentation_nontrivial _, eq_bot_or_eq_top := fun K => ?_ }
  by_contra hK
  push Not at hK
  have h₁ := he ψ N d hs hnj _ hkN rfl ⊥ K (bot_lt_iff_ne_bot.mpr hK.1)
  have h₂ := he ψ N d hs hnj _ hkN rfl K ⊤ (lt_top_iff_ne_top.mpr hK.2)
  have := hX
  rcases eq_bot_or_eq_top
      (SmoothRep.hom ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ N
        (∑ i, (d.segments i).rank) hkN).map (SmoothRep.subtype d.induced K))).range with h | h
  · rw [h] at h₁
    exact not_lt_bot h₁
  · rw [h] at h₂
    exact not_top_lt h₂

end UnlinkedSegmentSocleProductIrreducibleProof

/-- Zelevinsky (1980), Theorem 4.2, (2)⇒(1): a product of segment socles whose
multisegment is unlinked is irreducible. -/
theorem unlinkedSegmentSocleProductIrreducible {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    UnlinkedSegmentSocleProductIrreducible.{uF, uV} F T :=
  UnlinkedSegmentSocleProductIrreducibleProof.of_derivatives F T
    (HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T)
    (nonjuxtaposedSegmentSocleDerivativeStrictMono F T)
    (segmentSocleProductHighestDerivative F T)

end Langlands.Classification
