import Langlands.TraceFormula.BoundedCharacterSeparationProof
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Comparing two trace sums on a character fibre -/

universe uTest uLeft uRight uPlace uHecke

namespace Langlands.TraceFormula

/-- A positive scalar that can be chosen jointly for any two tests can be
chosen for the whole family. -/
theorem exists_common_pos_trace_scalar {Test : Type uTest} (twisted ordinary : Test → ℂ)
    (hpair : ∀ x y, ∃ c : ℝ, 0 < c ∧
      twisted x = (c : ℂ) * ordinary x ∧ twisted y = (c : ℂ) * ordinary y) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, twisted x = (c : ℂ) * ordinary x := by
  classical
  by_cases h : ∃ x, ordinary x ≠ 0
  · obtain ⟨x, hx⟩ := h
    obtain ⟨c, hc, hcx, _⟩ := hpair x x
    refine ⟨c, hc, fun y => ?_⟩
    obtain ⟨d, _, hdx, hdy⟩ := hpair x y
    have hd : (d : ℂ) = (c : ℂ) := mul_right_cancel₀ hx (hdx.symm.trans hcx)
    rwa [hd] at hdy
  · refine ⟨1, zero_lt_one, fun x => ?_⟩
    obtain ⟨c, _, hcx, _⟩ := hpair x x
    have hx : ordinary x = 0 := not_not.mp fun hne => h ⟨x, hne⟩
    simp [hx] at hcx ⊢
    exact hcx

/-- If two sums of products of bounded characters agree up to a fixed scalar
for all finite-place tests, their coefficient sums on each common character
fibre agree up to the same scalar. The characters in both families must
admit simultaneous complex conjugation by a single test at each place. -/
def BoundedCharacterTraceComparisonStatement : Prop :=
  ∀ (I : Type uLeft) (J : Type uRight) (W : Type uPlace) (H : W → Type uHecke)
    [∀ x, Semiring (H x)] [∀ x, Algebra ℂ (H x)]
    (χ : I ⊕ J → (x : W) → H x →ₐ[ℂ] ℂ)
    (a : I → ℂ) (b : J → ℂ) (c : ℂ),
    (∀ (x : W) (h : H x), ∃ C : ℝ, ∀ i, ‖χ i x h‖ ≤ C) →
    (∀ (x : W) (h : H x), ∃ h' : H x, ∀ i, χ i x h' = starRingEnd ℂ (χ i x h)) →
    (∀ (T : Finset W) (h : (x : W) → H x), ∃ A B : ℂ,
      HasSum (fun i => a i * ∏ x ∈ T, χ (.inl i) x (h x)) A ∧
      HasSum (fun j => b j * ∏ x ∈ T, χ (.inr j) x (h x)) B ∧ A = c * B) →
    ∀ i₀ : I,
      (∑' i : {i : I // ∀ x, χ (.inl i) x = χ (.inl i₀) x}, a i) =
        c * ∑' j : {j : J // ∀ x, χ (.inr j) x = χ (.inl i₀) x}, b j

/-- Bounded character separation on the disjoint union compares the sums on
the two fibres. -/
theorem boundedCharacterTraceComparison :
    BoundedCharacterTraceComparisonStatement.{uLeft, uRight, uPlace, uHecke} := by
  classical
  intro I J W H _ _ χ a b c hbound hconj hcompare i₀
  let coeff : I ⊕ J → ℂ := Sum.elim a (fun j => -(c * b j))
  obtain ⟨A₀, B₀, ha, hb, _⟩ := hcompare ∅ fun _ => 1
  simp only [Finset.prod_empty, mul_one] at ha hb
  have hcoeff : Summable coeff :=
    .sum coeff ha.summable (hb.mul_left c).neg.summable
  have htest (T : Finset W) (h : (x : W) → H x) :
      HasSum (fun i => coeff i * ∏ x ∈ T, χ i x (h x)) 0 := by
    obtain ⟨A, B, hA, hB, hAB⟩ := hcompare T h
    let term (i : I ⊕ J) := coeff i * ∏ x ∈ T, χ i x (h x)
    have hB' : HasSum (term ∘ Sum.inr) (-(c * B)) := by
      change HasSum (fun j => coeff (.inr j) * ∏ x ∈ T, χ (.inr j) x (h x)) (-(c * B))
      simpa only [coeff, Sum.elim_inr, neg_mul, mul_assoc] using (hB.mul_left c).neg
    have hsum := HasSum.sum (f := term) hA hB'
    rwa [hAB, add_neg_cancel] at hsum
  let fibre : Set (I ⊕ J) := {i | ∀ x, χ i x = χ (.inl i₀) x}
  have hzero : (∑' i, fibre.indicator coeff i) = 0 := by
    rw [← tsum_subtype]
    have hsep := boundedCharacterSeparation (I ⊕ J) W H χ coeff hcoeff hbound hconj htest
      (.inl i₀)
    exact hsep.tsum_eq
  let left : Set I := {i | ∀ x, χ (.inl i) x = χ (.inl i₀) x}
  let right : Set J := {j | ∀ x, χ (.inr j) x = χ (.inl i₀) x}
  have hleft : fibre.indicator coeff ∘ Sum.inl = left.indicator a := by
    funext i
    rfl
  have hright : fibre.indicator coeff ∘ Sum.inr = right.indicator (fun j => -(c * b j)) := by
    funext j
    rfl
  have hsL : Summable (fibre.indicator coeff ∘ Sum.inl) := by
    rw [hleft]
    exact ha.summable.indicator left
  have hsR : Summable (fibre.indicator coeff ∘ Sum.inr) := by
    rw [hright]
    exact (hb.mul_left c).neg.summable.indicator right
  rw [Summable.tsum_sum (f := fibre.indicator coeff) hsL hsR] at hzero
  change (∑' i, (fibre.indicator coeff ∘ Sum.inl) i) +
    (∑' j, (fibre.indicator coeff ∘ Sum.inr) j) = 0 at hzero
  rw [hleft, hright, ← tsum_subtype, ← tsum_subtype, tsum_neg, tsum_mul_left] at hzero
  change (∑' i : left, a i) = c * ∑' j : right, b j
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hzero)

end Langlands.TraceFormula
