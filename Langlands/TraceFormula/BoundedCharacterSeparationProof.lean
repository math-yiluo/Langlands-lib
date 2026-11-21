import Langlands.TraceFormula.BoundedCharacterSeparationStatement
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Proof of bounded character separation

For each character coordinate, a normalized squared difference from the reference
value gives a test with values in `[0, 1]`. Finite products and powers of these
tests converge pointwise to the fibre indicator. Tannery's theorem passes this
limit through the absolutely convergent sum.
-/

open Filter
open scoped Topology

universe u v w

namespace Langlands.TraceFormula

private theorem exists_local_test {ι : Type u} {A : Type w} [Semiring A] [Algebra ℂ A]
    (χ : ι → A →ₐ[ℂ] ℂ) (i₀ : ι) (h : A)
    (hbound : ∀ a, ∃ C : ℝ, ∀ i, ‖χ i a‖ ≤ C)
    (hconj : ∀ a, ∃ b, ∀ i, χ i b = starRingEnd ℂ (χ i a)) :
    ∃ (a : A) (q : ι → ℝ), (∀ i, χ i a = (q i : ℂ)) ∧
      (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧
      (∀ i, q i = 1 ↔ χ i h = χ i₀ h) := by
  let d : A := h + algebraMap ℂ A (-χ i₀ h)
  have hd (i : ι) : χ i d = χ i h - χ i₀ h := by
    simp [d, sub_eq_add_neg]
  obtain ⟨C, hC⟩ := hbound d
  obtain ⟨d', hd'⟩ := hconj d
  let D : ℝ := C ^ 2 + 1
  have hD : 0 < D := add_pos_of_nonneg_of_pos (sq_nonneg C) zero_lt_one
  let q (i : ι) : ℝ := 1 - ‖χ i d‖ ^ 2 / D
  refine ⟨1 + algebraMap ℂ A (-(D : ℂ)⁻¹) * (d * d'), q, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [q, map_add, map_one, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply,
      hd', Complex.mul_conj', Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_pow]
    rw [sub_eq_add_neg, div_eq_inv_mul, neg_mul]
  · intro i
    have hle : ‖χ i d‖ ^ 2 ≤ D :=
      (pow_le_pow_left₀ (norm_nonneg _) (hC i) 2).trans (le_add_of_nonneg_right zero_le_one)
    exact sub_nonneg.mpr ((div_le_one₀ hD).2 hle)
  · exact fun i => sub_le_self _ (div_nonneg (sq_nonneg _) hD.le)
  · intro i
    simp [q, hD.ne', hd, sub_eq_zero]

variable {ι : Type u} {W : Type v} {H : W → Type w} [∀ x, Semiring (H x)]
  [∀ x, Algebra ℂ (H x)]

/-- The functions realized by a choice of one local test at each of finitely many places. -/
private def characterTests (χ : ι → (x : W) → H x →ₐ[ℂ] ℂ) : Submonoid (ι → ℂ) where
  carrier := {f | ∃ (T : Finset W) (h : (x : W) → H x), ∀ i, (∏ x ∈ T, χ i x (h x)) = f i}
  one_mem' := ⟨∅, fun _ => 1, by simp⟩
  mul_mem' := by
    classical
    rintro f g ⟨T, h, hf⟩ ⟨U, k, hg⟩
    -- Extend each family by the unit, then multiply the tests at each place.
    let pad (S : Finset W) (a : (x : W) → H x) (x : W) : H x :=
      if x ∈ S then a x else 1
    refine ⟨T ∪ U, fun x => pad T h x * pad U k x, fun i => ?_⟩
    have extend (S : Finset W) (a : (x : W) → H x) (hS : S ⊆ T ∪ U) :
        (∏ x ∈ T ∪ U, χ i x (pad S a x)) = ∏ x ∈ S, χ i x (a x) := by
      calc
        _ = ∏ x ∈ S, χ i x (pad S a x) :=
          (Finset.prod_subset hS fun x _ hx => by simp [pad, hx]).symm
        _ = _ := Finset.prod_congr rfl fun x hx => by simp [pad, hx]
    simp only [map_mul, Finset.prod_mul_distrib, Pi.mul_apply]
    rw [extend T h Finset.subset_union_left, extend U k Finset.subset_union_right, hf, hg]

private theorem local_mem_characterTests (χ : ι → (x : W) → H x →ₐ[ℂ] ℂ)
    (x : W) (a : H x) : (fun i => χ i x a) ∈ characterTests χ := by
  classical
  exact ⟨{x}, fun y => if h : x = y then h ▸ a else 1, by simp⟩

/-- Vanishing of all finite product tests gives vanishing on each character fibre. -/
theorem boundedCharacterSeparation : BoundedCharacterSeparationStatement.{u, v, w} := by
  classical
  intro ι W H _ _ χ c hc hbound hconj hvanish i₀
  let fibre : Set ι := {i | ∀ x, χ i x = χ i₀ x}
  choose a q hq hnonneg hle_one heq using
    fun p : Sigma H => exists_local_test (fun i => χ i p.1) i₀ p.2 (hbound p.1) (hconj p.1)
  let approx (t : Finset (Sigma H) × ℕ) (i : ι) : ℝ := (∏ p ∈ t.1, q p i) ^ t.2
  let test (t : Finset (Sigma H) × ℕ) : ι → ℂ :=
    (∏ p ∈ t.1, fun i => χ i p.1 (a p)) ^ t.2
  have test_apply (t : Finset (Sigma H) × ℕ) (i : ι) : test t i = (approx t i : ℂ) := by
    simp [test, approx, hq]
  have prod_nonneg (S : Finset (Sigma H)) (i : ι) : 0 ≤ ∏ p ∈ S, q p i :=
    Finset.prod_nonneg fun p _ => hnonneg p i
  have prod_le_one (S : Finset (Sigma H)) (i : ι) : (∏ p ∈ S, q p i) ≤ 1 :=
    Finset.prod_le_one₀ (fun p _ => hnonneg p i) (fun p _ => hle_one p i)
  have hpoint (i : ι) : Tendsto (fun t => approx t i) atTop
      (𝓝 (fibre.indicator (fun _ => (1 : ℝ)) i)) := by
    by_cases hi : i ∈ fibre
    · have hall (p : Sigma H) : q p i = 1 := (heq p i).2 (DFunLike.congr_fun (hi p.1) p.2)
      simp [approx, hall, hi]
    · have hex : ∃ p : Sigma H, χ i p.1 p.2 ≠ χ i₀ p.1 p.2 := by
        by_contra! hn
        exact hi fun x => AlgHom.ext fun h => hn ⟨x, h⟩
      obtain ⟨p, hp⟩ := hex
      have hlt : q p i < 1 := lt_of_le_of_ne (hle_one p i) ((heq p i).not.mpr hp)
      have hsnd : Tendsto (fun t : Finset (Sigma H) × ℕ => t.2) atTop atTop :=
        tendsto_atTop.2 fun n => (eventually_ge_atTop ((∅ : Finset (Sigma H)), n)).mono
          fun _ ht => ht.2
      rw [Set.indicator_of_notMem hi]
      refine tendsto_const_nhds.squeeze'
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (hnonneg p i) hlt).comp hsnd)
        (Eventually.of_forall fun t => pow_nonneg (prod_nonneg t.1 i) t.2) ?_
      filter_upwards [eventually_ge_atTop (({p} : Finset (Sigma H)), (0 : ℕ))] with t ht
      have hle : (∏ b ∈ t.1, q b i) ≤ q p i := by
        simpa using Finset.prod_le_prod_of_subset_of_le_one₀ ht.1
          (fun b _ => hnonneg b i) (fun b _ _ => hle_one b i)
      exact pow_le_pow_left₀ (prod_nonneg t.1 i) hle t.2
  have hlim : Tendsto (fun t => ∑' i, c i * test t i) atTop (𝓝 (∑' i, fibre.indicator c i)) := by
    refine tendsto_tsum_of_dominated_convergence hc.norm ?_ (Eventually.of_forall ?_)
    · intro i
      have hcast := ((Complex.continuous_ofReal.tendsto _).comp (hpoint i)).const_mul (c i)
      by_cases hi : i ∈ fibre <;> simpa [Function.comp_def, test_apply, hi] using hcast
    · intro t i
      rw [norm_mul, test_apply, Complex.norm_of_nonneg (pow_nonneg (prod_nonneg t.1 i) t.2)]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (prod_nonneg t.1 i) (prod_le_one t.1 i))
  have hzero (t : Finset (Sigma H) × ℕ) : (∑' i, c i * test t i) = 0 := by
    have ht : test t ∈ characterTests χ :=
      (characterTests χ).pow_mem
        ((characterTests χ).prod_mem fun p _ => local_mem_characterTests χ p.1 (a p)) t.2
    obtain ⟨T, h, hh⟩ := ht
    simpa only [hh] using (hvanish T h).tsum_eq
  have htsum : (∑' i, fibre.indicator c i) = 0 :=
    tendsto_nhds_unique hlim (by simp only [hzero, tendsto_const_nhds])
  have hs : Summable (fun i : fibre => c i) := hc.subtype fibre
  rw [← tsum_subtype] at htsum
  exact htsum ▸ hs.hasSum

end Langlands.TraceFormula
