import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectralPowerBoundProof
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Evaluation
import Mathlib.Topology.MetricSpace.Contracting

/-! # Polynomial fixed points with spectral bounds -/

noncomputable section

universe u v

namespace Langlands.Analytic

open scoped NNReal

private theorem norm_sub_pow_succ_le
    {A : Type u} [NormedCommRing A] [NormOneClass A] [IsUltrametricDist A]
    {r : ℝ} (hr : 0 ≤ r) {x y : A} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ r ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : ‖x ^ (n + 1)‖ ≤ r ^ (n + 1) :=
      (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg x) hx _)
    calc
      ‖x ^ (n + 1 + 1) - y ^ (n + 1 + 1)‖ =
          ‖x ^ (n + 1) * (x - y) + (x ^ (n + 1) - y ^ (n + 1)) * y‖ := by
        congr 1
        rw [pow_succ x, pow_succ y]
        ring
      _ ≤ max ‖x ^ (n + 1) * (x - y)‖ ‖(x ^ (n + 1) - y ^ (n + 1)) * y‖ :=
        IsUltrametricDist.norm_add_le_max _ _
      _ ≤ r ^ (n + 1) * ‖x - y‖ := by
        apply max_le
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hpow (norm_nonneg _))
        · calc
            ‖(x ^ (n + 1) - y ^ (n + 1)) * y‖ ≤ (r ^ n * ‖x - y‖) * r :=
              (norm_mul_le _ _).trans
                (mul_le_mul ih hy (norm_nonneg _) (mul_nonneg (pow_nonneg hr _) (norm_nonneg _)))
            _ = r ^ (n + 1) * ‖x - y‖ := by rw [pow_succ]; ring

private theorem exists_boundedPolynomialFixedPoint
    {A : Type u} [NormedCommRing A] [NormOneClass A] [IsUltrametricDist A] [CompleteSpace A]
    {ι : Type v} [Fintype ι] (d : ι → ℕ) (c : A) (b : ι → A)
    {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hq' : q < 1) (hc : ‖c‖ ≤ r)
    (hb : ∀ i, ‖b i‖ * r ^ d i ≤ q) :
    ∃ y : A, y = c + ∑ i, b i * y ^ (d i + 1) ∧ ‖y‖ ≤ r := by
  let F (x : A) := c + ∑ i, b i * x ^ (d i + 1)
  have hdiff (x y : A) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
      ‖F x - F y‖ ≤ q * ‖x - y‖ := by
    simp only [F, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, ← mul_sub]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hq (norm_nonneg _))
    intro i _
    calc
      ‖b i * (x ^ (d i + 1) - y ^ (d i + 1))‖ ≤
          ‖b i‖ * (r ^ d i * ‖x - y‖) :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (norm_sub_pow_succ_le hr hx hy (d i)) (norm_nonneg _))
      _ = (‖b i‖ * r ^ d i) * ‖x - y‖ := (mul_assoc _ _ _).symm
      _ ≤ q * ‖x - y‖ := mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)
  have hzero : F 0 = c := by simp [F]
  let B := Metric.closedBall (0 : A) r
  have member (x : A) : x ∈ B ↔ ‖x‖ ≤ r := by simp [B, Metric.mem_closedBall, dist_zero_right]
  have hF (x : A) (hx : ‖x‖ ≤ r) : ‖F x‖ ≤ r := by
    have h := hdiff x 0 hx (by simpa using hr)
    rw [hzero, sub_zero] at h
    calc
      ‖F x‖ = ‖(F x - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ max ‖F x - c‖ ‖c‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ r := max_le (h.trans ((mul_le_of_le_one_left (norm_nonneg x) hq'.le).trans hx)) hc
  let f (x : B) : B := ⟨F x, (member _).mpr (hF x ((member _).mp x.2))⟩
  let : CompleteSpace B := Metric.isClosed_closedBall.isComplete.completeSpace_coe
  let : Nonempty B := ⟨⟨0, (member _).mpr (by simpa using hr)⟩⟩
  let q₀ : ℝ≥0 := ⟨q, hq⟩
  have hf : ContractingWith q₀ f := by
    refine ⟨hq', LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    change dist (F x) (F y) ≤ q * dist (x : A) (y : A)
    simpa only [dist_eq_norm] using hdiff x y ((member _).mp x.2) ((member _).mp y.2)
  let y := hf.fixedPoint f
  have hy : f y = y := hf.fixedPoint_isFixedPt
  exact ⟨y, (congrArg Subtype.val hy).symm, (member _).mp y.2⟩

namespace PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A polynomial with spectrally small constant term and uniformly contracting nonconstant
terms has a fixed point in the prescribed spectral ball of a presented affinoid algebra. -/
theorem exists_spectralPolynomialFixedPoint
    (A : PresentedAffinoidAlgebra K) {ι : Type v} [Fintype ι] (d : ι → ℕ)
    (c : A) (b : ι → A) {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hq' : q < 1)
    (hc : ∀ x : BanachSpectrum A, x c ≤ r)
    (hb : ∀ (i : ι) (x : BanachSpectrum A), x (b i) * r ^ d i ≤ q) :
    ∃ y : A, y = c + ∑ i, b i * y ^ (d i + 1) ∧ ∀ x : BanachSpectrum A, x y ≤ r := by
  let R : PositivePolyradius (Option ι) :=
    ⟨fun i => i.elim r (fun j => q / r ^ d j), fun i => by
      cases i with
      | none => exact hr
      | some j => exact div_pos hq (pow_pos hr _)⟩
  let X := GeneralizedTateAlgebra.X R K
  have hX (i : Option ι) : ‖X i‖ = R i := GeneralizedTateAlgebra.norm_X_of_normOne R K i
  have hc' : ‖X none‖ ≤ r := (hX none).le
  have hb' (i : ι) : ‖X (some i)‖ * r ^ d i ≤ q := by
    rw [hX]
    change (q / r ^ d i) * r ^ d i ≤ q
    exact (div_mul_cancel₀ _ (pow_pos hr _).ne').le
  obtain ⟨Y, hY, hYn⟩ :=
    exists_boundedPolynomialFixedPoint d (X none) (X ∘ some) hr.le hq.le hq' hc' hb'
  let a : Option ι → A := fun i => i.elim c b
  have ha (i : Option ι) : ∀ x : BanachSpectrum A, x (a i) ≤ R i := by
    cases i with
    | none => exact hc
    | some j => exact fun x => (le_div_iff₀ (pow_pos hr _)).mpr (hb j x)
  have hmono : GeneralizedTateAlgebra.HasBoundedMonomials R A a :=
    (GeneralizedTateAlgebra.hasBoundedMonomials_iff_radiusBoundedPowers R A a).mpr
      fun i => spectralPowerBound A (a i) (R i) (R.positive i) (ha i)
  let φ := GeneralizedTateAlgebra.evaluateHom R K A a hmono
  have hφ (i : Option ι) : φ (X i) = a i := GeneralizedTateAlgebra.evaluate_X R K A a i
  refine ⟨φ Y, ?_, fun x => ((BanachSpectrum.comap φ.toBoundedRingHom x).le_norm Y).trans hYn⟩
  change φ Y = a none + ∑ i, a (some i) * (φ Y) ^ (d i + 1)
  simpa only [Function.comp_apply, map_add, map_sum, map_mul, map_pow, hφ] using congrArg φ hY

end PresentedAffinoidAlgebra

end Langlands.Analytic
