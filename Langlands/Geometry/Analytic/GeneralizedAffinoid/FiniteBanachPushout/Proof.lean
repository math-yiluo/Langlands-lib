import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Statement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushoutAdmissibility

/-! # Finite Banach base change in the actual affinoid pushout -/

noncomputable section

universe u v w

open Function Filter Topology
open scoped TensorProduct NNReal

namespace Langlands.Analytic

/-- Iterated approximate lifts give exact controlled lifts, without any
nontrivial-valuation hypothesis on the scalar field. -/
theorem exists_normControlledLifts_of_approx
    {K : Type u} [NormedField K]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]
    (L : E →L[K] F) {C : ℝ} (hC : 0 ≤ C)
    (happrox : ∀ y, ∃ x, dist (L x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) :
    ∃ D > 0, ∀ y, ∃ x, L x = y ∧ ‖x‖ ≤ D * ‖y‖ := by
  choose g hg using happrox
  let h y := y - L (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y => ?_⟩
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n ih =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let a n := g (h^[n] y)
  have hale : ∀ n, ‖a n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n => by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hnle n) hC
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNa : Summable fun n => ‖a n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) hale ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have sa : Summable a := sNa.of_norm
  let x := tsum a
  have hxn : ‖x‖ ≤ (2 * C + 1) * ‖y‖ := by
    calc
      ‖x‖ ≤ ∑' n, ‖a n‖ := norm_tsum_le_tsum_norm sNa
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNa.tsum_le_tsum hale (Summable.mul_right _ summable_geometric_two)
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  have hsum : ∀ n : ℕ, L (∑ i ∈ Finset.range n, a i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [L.map_zero]
    | succ n ih => rw [Finset.sum_range_succ, L.map_add, ih, iterate_succ_apply', sub_add]
  have hlim : Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop (𝓝 x) :=
    sa.hasSum.tendsto_sum_nat
  have hL : Tendsto (fun n => L (∑ i ∈ Finset.range n, a i)) atTop (𝓝 (L x)) :=
    (L.continuous.tendsto _).comp hlim
  simp only [hsum] at hL
  have hy : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;>
      norm_num
  exact ⟨x, by simpa only [sub_zero] using tendsto_nhds_unique hL hy, hxn⟩

namespace PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

omit [CompleteSpace K] in
/-- Finite-max tensor representations yield coefficients over the changed base
with a bound independent of the number of tensor terms. -/
theorem exists_coefficient_lift_representation
    {n : ℕ} (b : Fin n → B) {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hb : ∀ y : B, ∃ a : Fin n → A,
      f.coefficientMap b a = y ∧ ‖a‖ ≤ M * ‖y‖)
    (hg : ∀ a : A, ‖g a‖ ≤ N * ‖a‖)
    (t : CompletedTensorAlgebra.Algebraic K B C)
    (r : UltrametricTensorSeminorm.Representation K B C t) :
    ∃ c : Fin n → C,
      (rightMap f g).coefficientMap (fun j => leftMap f g (b j)) c =
        CompletedTensorAlgebra.algebraicLift (leftMap f g) (rightMap f g) t ∧
      ‖c‖ ≤ (N * M) * (r.value : ℝ) := by
  classical
  let : Fintype r.ι := r.fintype
  choose a ha han using fun i : r.ι => hb (r.left i)
  let c : Fin n → C := fun j => ∑ i, g (a i j) * r.right i
  refine ⟨c, ?_, ?_⟩
  · have hcondition (x : A) : leftMap f g (f x) = rightMap f g (g x) :=
      congrArg (fun k : BoundedAlgHom K A (algebra f g) => k x) (condition f g)
    have hs : CompletedTensorAlgebra.algebraicLift (leftMap f g) (rightMap f g) t =
        ∑ i, leftMap f g (r.left i) * rightMap f g (r.right i) := by
      calc
        _ = CompletedTensorAlgebra.algebraicLift (leftMap f g) (rightMap f g)
            (∑ i, r.left i ⊗ₜ[K] r.right i) :=
          congrArg (CompletedTensorAlgebra.algebraicLift (leftMap f g) (rightMap f g))
            r.sum_eq.symm
        _ = _ := (map_sum (CompletedTensorAlgebra.algebraicLift (leftMap f g) (rightMap f g))
          (fun i => (r.left i ⊗ₜ[K] r.right i : CompletedTensorAlgebra.Algebraic K B C))
          Finset.univ).trans (Finset.sum_congr rfl fun i _ =>
            CompletedTensorAlgebra.algebraicLift_tmul _ _ (r.left i) (r.right i))
    rw [hs, BoundedAlgHom.coefficientMap_apply]
    simp only [c, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ha i, BoundedAlgHom.coefficientMap_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hcondition]
    ring
  · refine (pi_norm_le_iff_of_nonneg
      (mul_nonneg (mul_pos hN hM).le r.value.coe_nonneg)).2 fun j => ?_
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg (mul_pos hN hM).le r.value.coe_nonneg)
    intro i _
    calc
      ‖g (a i j) * r.right i‖ ≤ ‖g (a i j)‖ * ‖r.right i‖ := norm_mul_le _ _
      _ ≤ (N * ‖a i j‖) * ‖r.right i‖ :=
        mul_le_mul_of_nonneg_right (hg _) (norm_nonneg _)
      _ ≤ (N * (M * ‖r.left i‖)) * ‖r.right i‖ := by
        gcongr
        exact (norm_le_pi_norm (a i) j).trans (han i)
      _ = (N * M) * (‖r.left i‖ * ‖r.right i‖) := by ring
      _ ≤ (N * M) * (r.value : ℝ) := mul_le_mul_of_nonneg_left
        (by exact_mod_cast r.le_value i) (mul_pos hN hM).le

/-- Finite Banach maps remain finite Banach after arbitrary bounded base
change in the actual closed-quotient affinoid pushout. -/
theorem rightMap_isFiniteBanach (hf : f.IsFiniteBanach) :
    (rightMap f g).IsFiniteBanach := by
  classical
  obtain ⟨n, b, M, hM, hb⟩ := hf
  obtain ⟨N, hN, hg⟩ := g.bounded
  obtain ⟨H, hH, hlift⟩ :=
    (tensorMap f g).isAdmissibleEpi_iff_normControlledLifts.mp
      (tensorMap_isAdmissibleEpi f g)
  obtain ⟨P, hP, hbound⟩ := (tensorMap f g).bounded
  let d : Fin n → algebra f g := fun j => leftMap f g (b j)
  have happrox : ∀ z : algebra f g, ∃ c : Fin n → C,
      dist ((rightMap f g).coefficientMap d c) z ≤ 1 / 2 * ‖z‖ ∧
      ‖c‖ ≤ ((N * M) * (H + 1)) * ‖z‖ := by
    intro z
    by_cases hz : z = 0
    · subst z
      exact ⟨0, by simp, by simp⟩
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨y, hy, hyn⟩ := hlift z
    let ε : ℝ := ‖z‖ / (2 * (P + 1))
    have hden : 0 < 2 * (P + 1) := by positivity
    have hε : 0 < ε := div_pos hzpos hden
    have hεz : ε ≤ ‖z‖ := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg hP.le (norm_nonneg z)]
    obtain ⟨t, ht⟩ :=
      (CompletedTensorAlgebra.denseRange_toCompletion K B C).exists_dist_lt y hε
    rw [dist_eq_norm] at ht
    have htn : ‖t‖ < (H + 1) * ‖z‖ := by
      calc
        ‖t‖ = ‖CompletedTensorAlgebra.toCompletion K B C t‖ :=
          (UniformSpace.Completion.norm_coe t).symm
        _ ≤ ‖y‖ + ‖y - CompletedTensorAlgebra.toCompletion K B C t‖ := by
          simpa only [sub_sub_cancel] using
            norm_sub_le y (y - CompletedTensorAlgebra.toCompletion K B C t)
        _ < H * ‖z‖ + ε := add_lt_add_of_le_of_lt hyn ht
        _ ≤ (H + 1) * ‖z‖ := by nlinarith [hεz]
    let R : ℝ≥0 := ⟨(H + 1) * ‖z‖, by positivity⟩
    have hseminorm : UltrametricTensorSeminorm.seminormFun
        (t : B ⊗[K] C) < R := by
      exact_mod_cast htn
    let : Nonempty (UltrametricTensorSeminorm.Representation K B C t) :=
      UltrametricTensorSeminorm.Representation.nonempty (t : B ⊗[K] C)
    obtain ⟨r, hr⟩ := exists_lt_of_ciInf_lt
      (f := fun r : UltrametricTensorSeminorm.Representation K B C t => r.value)
      hseminorm
    obtain ⟨c, hc, hcn⟩ :=
      exists_coefficient_lift_representation f g b hM hN hb hg t r
    refine ⟨c, ?_, ?_⟩
    · have hceq : (rightMap f g).coefficientMap d c =
          tensorMap f g (CompletedTensorAlgebra.toCompletion K B C t) :=
        hc.trans (CompletedTensorAlgebra.lift_toCompletion _ _ t).symm
      rw [hceq]
      calc
        dist (tensorMap f g (CompletedTensorAlgebra.toCompletion K B C t)) z =
            ‖tensorMap f g (CompletedTensorAlgebra.toCompletion K B C t - y)‖ := by
          rw [map_sub, hy, dist_eq_norm]
        _ ≤ P * ‖CompletedTensorAlgebra.toCompletion K B C t - y‖ := hbound _
        _ ≤ P * ε := mul_le_mul_of_nonneg_left (by
          simpa only [norm_sub_rev] using ht.le) hP.le
        _ ≤ 1 / 2 * ‖z‖ := by
          dsimp [ε]
          rw [← mul_div_assoc]
          apply (div_le_iff₀ hden).2
          nlinarith [norm_nonneg z]
    · calc
        ‖c‖ ≤ (N * M) * (r.value : ℝ) := hcn
        _ ≤ (N * M) * ((H + 1) * ‖z‖) := mul_le_mul_of_nonneg_left
          (by exact_mod_cast hr.le) (mul_pos hN hM).le
        _ = ((N * M) * (H + 1)) * ‖z‖ := (mul_assoc _ _ _).symm
  obtain ⟨D, hD, hcoeff⟩ := exists_normControlledLifts_of_approx
    ((rightMap f g).coefficientMap d) (by positivity) happrox
  exact ⟨n, d, D, hD, hcoeff⟩

/-- Exact proof of the published unrestricted finite Banach pushout statement. -/
theorem finiteBanachPushout : FiniteBanachPushoutStatement K := by
  intro A B C f g hf
  exact rightMap_isFiniteBanach f g hf

end PresentedAffinoidAlgebra.AffinoidPushout
end Langlands.Analytic
