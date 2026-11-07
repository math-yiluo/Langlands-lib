import Langlands.Representation.RankinSelberg.SchurPairSummability
import Langlands.Representation.RankinSelberg.AbsoluteSeriesEvaluation

/-! # Analytic Cauchy identity on individual partitions -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

/-- Forget the finite coordinate bound in a degree partition. -/
def degreePartitionNatWeight {n d : ℕ} (α : DegreePartition n d) : Fin (n + 1) → ℕ :=
  fun i => (α.val i).val

/-- All natural partitions are indexed exactly by their degree and a finite degree partition. -/
def degreePartitionEquiv (n : ℕ) :
    (Σ d : ℕ, DegreePartition n d) ≃ {α : Fin (n + 1) → ℕ // Antitone α} :=
  Equiv.ofBijective
    (fun β => ⟨degreePartitionNatWeight β.2, fun _ _ h => β.2.property.1 h⟩) (by
      constructor
      · rintro ⟨d, α⟩ ⟨e, β⟩ h
        have hv := congrArg Subtype.val h
        have hd := congrArg (fun a : Fin (n + 1) → ℕ => ∑ i, a i) hv
        change (∑ i, (α.val i).val) = ∑ i, (β.val i).val at hd
        rw [α.property.2, β.property.2] at hd
        subst e
        congr 1
        apply Subtype.ext
        funext i
        apply Fin.ext
        exact congrFun hv i
      · intro α
        let d := ∑ i, α.val i
        have hbound (i : Fin (n + 1)) : α.val i < d + 1 := by
          have h := Finset.single_le_sum (fun j _ => Nat.zero_le (α.val j))
            (Finset.mem_univ i)
          omega
        refine ⟨⟨d, ⟨fun i => ⟨α.val i, hbound i⟩, ?_, rfl⟩⟩, ?_⟩
        · intro i j hij
          exact α.property hij
        · rfl)

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The degree coefficient times its parameter power is the finite sum of the individual terms. -/
theorem coeff_complexCauchySeries_mul_pow {n : ℕ}
    (x : σ → ℂ) (y : Fin (n + 1) → ℂ) (t : ℂ) (d : ℕ) :
    PowerSeries.coeff d (complexCauchySeries x y) * t ^ d =
      ∑ α : DegreePartition n d, schurPairTerm x y t (degreePartitionNatWeight α) := by
  rw [coeff_complexCauchySeries, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  have hd : (∑ i, degreePartitionNatWeight α i) = d := α.property.2
  simp only [schurPairTerm]
  rw [hd]
  rfl

set_option maxHeartbeats 800000 in
/-- Absolute convergence permits regrouping the individual partitions by their total degree. -/
theorem tsum_schurPairTerm_eq_seriesValue {n : ℕ}
    (x : σ → ℂ) (y : Fin (n + 1) → ℂ) (t : ℂ)
    (h : Summable (fun α : {α : Fin (n + 1) → ℕ // Antitone α} =>
      ‖schurPairTerm x y t α.val‖)) :
    (∑' α : {α : Fin (n + 1) → ℕ // Antitone α}, schurPairTerm x y t α.val) =
      seriesValue (complexCauchySeries x y) t := by
  have hsum : Summable (fun α : {α : Fin (n + 1) → ℕ // Antitone α} =>
      schurPairTerm x y t α.val) := h.of_norm
  have hs : Summable (fun β : Σ d : ℕ, DegreePartition n d =>
      schurPairTerm x y t (degreePartitionNatWeight β.2)) :=
    (degreePartitionEquiv n).summable_iff.mpr hsum
  rw [← (degreePartitionEquiv n).tsum_eq
    (fun α => schurPairTerm x y t α.val)]
  change (∑' β : Σ d : ℕ, DegreePartition n d,
    schurPairTerm x y t (degreePartitionNatWeight β.2)) = _
  rw [Summable.tsum_sigma' (fun d => (hasSum_fintype _).summable) hs]
  unfold seriesValue
  apply tsum_congr
  intro d
  rw [tsum_fintype, coeff_complexCauchySeries_mul_pow]

/-- On a positive disk the individual partition sum converges absolutely to the Euler product. -/
theorem exists_schurCauchy_radius {n : ℕ} (x : σ → ℂ) (y : Fin (n + 1) → ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      Summable (fun α : {α : Fin (n + 1) → ℕ // Antitone α} =>
        ‖schurPairTerm x y t α.val‖) ∧
      (∑' α : {α : Fin (n + 1) → ℕ // Antitone α}, schurPairTerm x y t α.val) =
        (∏ j : Fin (n + 1), ∏ i : σ, (1 - x i * y j * t))⁻¹ := by
  obtain ⟨r, hr, hs⟩ := exists_schurPartition_radius (n + 1) x y
  let B : ℝ := 1 + ∑ j : Fin (n + 1), ∑ i : σ, ‖x i * y j‖
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨min r B⁻¹, lt_min hr (inv_pos.mpr hB), fun t ht => ?_⟩
  have ht1 := (lt_min_iff.mp ht).1
  have ht2 := (lt_min_iff.mp ht).2
  have hpair (i : σ) (j : Fin (n + 1)) : ‖x i * y j * t‖ < 1 := by
    have hi := Finset.single_le_sum (fun a _ => norm_nonneg (x a * y j))
      (Finset.mem_univ i)
    have hj : (∑ a : σ, ‖x a * y j‖) ≤ ∑ b : Fin (n + 1), ∑ a : σ, ‖x a * y b‖ :=
      Finset.single_le_sum
      (fun b _ => Finset.sum_nonneg (fun a _ => norm_nonneg (x a * y b)))
      (Finset.mem_univ j)
    have hab : ‖x i * y j‖ ≤ B := by dsimp [B]; linarith
    rw [norm_mul]
    calc
      _ ≤ B * ‖t‖ := mul_le_mul_of_nonneg_right hab (norm_nonneg t)
      _ < B * B⁻¹ := mul_lt_mul_of_pos_left ht2 hB
      _ = 1 := mul_inv_cancel₀ hB.ne'
  exact ⟨hs t ht1, (tsum_schurPairTerm_eq_seriesValue x y t (hs t ht1)).trans
    (seriesValue_complexCauchySeries x y t hpair)⟩

end Langlands.GeneralLinear.Spherical
