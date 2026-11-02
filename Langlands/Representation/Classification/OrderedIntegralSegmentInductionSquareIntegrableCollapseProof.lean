import Langlands.Representation.Classification.OrderedIntegralSegmentInductionSquareIntegrableCollapseStatement
import Langlands.Representation.Classification.OrderedRunFirstNonpositiveProof
import Langlands.Representation.Classification.SegmentOccurrenceToFront
import Langlands.Representation.Exponents.BlockTensorScalarRealPart
import Langlands.Representation.Exponents.SquareIntegrableInductionEmbeddingConeProof
import Mathlib.Tactic

/-! # The first nonpositive interval contradicts the strict scalar cone -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory
open scoped BigOperators

universe uF uV

private theorem support_subset_of_integral_endpoints
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
    {Δ Γ : T.Segment.{max uF uV,uF}}
    {ρ : T.CuspidalDatum.{max uF uV,uF}} {a b c d : ℤ}
    (hΔ : Δ.HasIntegralCoordinates ρ a b) (hΓ : Γ.HasIntegralCoordinates ρ c d)
    (hca : c ≤ a) (hbd : b ≤ d) : Δ.support ⊆ Γ.support := by
  intro σ hσ
  obtain ⟨k, hak, hkb, hk⟩ := hΔ.mem_support_iff.mp hσ
  exact hΓ.mem_support_iff.mpr ⟨k, hca.trans hak, hkb.trans hbd, hk⟩

/-- The supplied actual commutation moves the first nonpositive interval to
the first position, where the strict scalar cone excludes multiple factors. -/
theorem orderedIntegralSegmentInductionSquareIntegrableCollapse
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    OrderedIntegralSegmentInductionSquareIntegrableCollapse.{uF,uV} F T := by
  classical
  let := T.topology
  intro hcomm n hn π _ hsq d hd hemb ρ a b hcoord ha t c hc hnorm
  have hr : 0 < d.length := by
    by_contra h
    let : IsEmpty (Fin d.length) := ⟨fun i => by have := i.isLt; omega⟩
    have hz : n = 0 := by simpa using d.degree_sum.symm
    omega
  let : NeZero d.length := ⟨by omega⟩
  let x : Fin d.length → ℝ := fun i =>
    ((d.segments i).degree : ℝ) * (t + ((a i : ℝ) + (b i : ℝ)) / 2)
  have hcone : ∀ e : Equiv.Perm (Fin d.length),
      SmoothRep.IsSubrepresentation π (d.permute e).induced →
      Exponents.IsPositiveRootCone (x ∘ e) := by
    intro e he
    obtain ⟨hscalar, hx⟩ := blockTensorScalarRealPart F T n d.shape d.blocks c x hc hnorm e
    exact squareIntegrableInductionEmbeddingCone p F T n hn π hsq
      (d.shape.permute e) (FiniteTensor.externalSmoothObject (fun i => d.blocks (e i)))
      he _ hscalar (x ∘ e) hx
  have hzero : ∑ i, x i = 0 := by
    simpa only [Equiv.coe_refl, Function.comp_id] using (hcone (Equiv.refl _) hemb).1
  have htotal :
      (∑ i, ((d.segments i).degree : ℝ) *
        ((t + (a i : ℝ)) + (t + (b i : ℝ)))) ≤ 0 := by
    have heq :
        (∑ i, ((d.segments i).degree : ℝ) *
          ((t + (a i : ℝ)) + (t + (b i : ℝ)))) = 2 * ∑ i, x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [x]
      ring
    rw [heq, hzero, mul_zero]
  have hmono : Monotone (fun i => t + (a i : ℝ)) := by
    intro i j hij
    have h : (a i : ℝ) ≤ (a j : ℝ) := by exact_mod_cast ha hij
    linarith
  obtain ⟨i, hi, hprev, _⟩ := orderedRunFirstNonpositive d.length hr
    (fun i => (d.segments i).degree) (fun i => t + (a i : ℝ))
    (fun i => t + (b i : ℝ)) (fun i => (d.segments i).degree_pos) hmono htotal
  have hunlinked : ∀ j : Fin d.length, j < i →
      ¬ (d.segments j).IsLinked (d.segments i) := by
    intro j hji hlinked
    apply hlinked.1
    apply support_subset_of_integral_endpoints (hcoord j) (hcoord i)
    · have h := (hprev j hji).2.1
      have hreal : (b i : ℝ) ≤ (b j : ℝ) := by linarith
      exact_mod_cast hreal
    · exact ha hji.le
  obtain ⟨E⟩ := segmentOccurrenceToFront F T hcomm d hd i hunlinked
  let e := (Fin.cycleRange i).symm
  have he : SmoothRep.IsSubrepresentation π (d.permute e).induced := by
    obtain ⟨f, hf⟩ := hemb
    let L := SmoothRep.equivOfIso E
    exact ⟨SmoothRep.ofHom (L.toIntertwiningMap.comp (SmoothRep.hom f)),
      L.injective.comp hf⟩
  have hxi : x i ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
    linarith
  by_contra hlen
  have hmany : 1 < d.length := by omega
  have hpositive := (hcone e he).2 1 (by omega) hmany
  have hfilter :
      Finset.univ.filter (fun j : Fin d.length => (j : ℕ) < 1) = {0} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      apply Fin.ext
      change (j : ℕ) = 0
      omega
    · intro hj
      subst j
      simp
  have hfirst : Exponents.partialSum (x ∘ e) 1 = x i := by
    simp only [Exponents.partialSum, hfilter, Finset.sum_singleton,
      Function.comp_apply, e, Fin.cycleRange_symm_zero]
  rw [hfirst] at hpositive
  exact (not_lt_of_ge hxi) hpositive

end Langlands.Classification
