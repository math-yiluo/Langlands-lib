import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Continuous one-parameter groups in a complete normed algebra are exponentials -/

noncomputable section

open NormedSpace

set_option autoImplicit false

namespace Langlands.Analysis.OneParameter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp (x + y) = exp x * exp y` for commuting elements of a complete normed real algebra. -/
theorem exp_add_of_commute_real {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    (by rw [expSeries_radius_eq_top]; exact edist_lt_top _ _)
    (by rw [expSeries_radius_eq_top]; exact edist_lt_top _ _)

/-- An element commuting with every value of a continuous function commutes with its
interval integral. -/
private theorem commute_intervalIntegral {M : ℝ → 𝔸} (hM : Continuous M) {Z : 𝔸}
    (hZ : ∀ s, Commute Z (M s)) (a b : ℝ) : Commute Z (∫ s in a..b, M s) := by
  have hint : IntervalIntegrable M MeasureTheory.volume a b := hM.intervalIntegrable a b
  have hl := (ContinuousLinearMap.mul ℝ 𝔸 Z).intervalIntegral_comp_comm hint
  have hr := ((ContinuousLinearMap.mul ℝ 𝔸).flip Z).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at hl hr
  change Z * (∫ s in a..b, M s) = (∫ s in a..b, M s) * Z
  rw [← hl, ← hr]
  exact intervalIntegral.integral_congr fun s _ => (hZ s).eq

/-- **Continuous one-parameter groups are exponentials.** A continuous `M : ℝ → 𝔸` with
`M 0 = 1` and `M (s + t) = M s * M t` is `t ↦ exp (t • X)` for an element `X` that commutes with
everything commuting with all values of `M`. -/
theorem exists_exp_of_continuous_add_mul (M : ℝ → 𝔸) (hM : Continuous M) (h0 : M 0 = 1)
    (hadd : ∀ s t, M (s + t) = M s * M t) :
    ∃ X : 𝔸, (∀ t : ℝ, M t = exp (t • X)) ∧
      ∀ Z : 𝔸, (∀ s, Commute Z (M s)) → Commute Z X := by
  -- A small interval on which `M` is close to `1`.
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hM.continuousAt (1 / 2 : ℝ) (by norm_num)
  set ε : ℝ := δ / 2 with hε_def
  have hε : 0 < ε := by positivity
  set I : 𝔸 := ∫ s in (0 : ℝ)..ε, M s with hI_def
  have hIbound : ‖ε⁻¹ • I - 1‖ ≤ 1 / 2 := by
    have hsub : I - ε • (1 : 𝔸) = ∫ s in (0 : ℝ)..ε, (M s - 1) := by
      rw [intervalIntegral.integral_sub (hM.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, sub_zero]
    have hle : ‖∫ s in (0 : ℝ)..ε, (M s - 1)‖ ≤ 1 / 2 * |ε - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le hε.le] at hs
      have hds : dist s 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
        linarith [hs.2]
      have h := hclose hds
      rw [h0, dist_eq_norm] at h
      exact h.le
    have heq : ε⁻¹ • I - 1 = ε⁻¹ • (I - ε • (1 : 𝔸)) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    rw [heq, norm_smul, hsub, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
    rw [sub_zero, abs_of_pos hε] at hle
    calc ε⁻¹ * ‖∫ s in (0 : ℝ)..ε, (M s - 1)‖ ≤ ε⁻¹ * (1 / 2 * ε) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hε.le)
      _ = 1 / 2 := by field_simp
  -- `ε⁻¹ • I` is a unit, hence so is `I`.
  have hsmall : ‖1 - ε⁻¹ • I‖ < 1 := by
    rw [norm_sub_rev]
    linarith
  let u : 𝔸ˣ := Units.oneSub (1 - ε⁻¹ • I) hsmall
  have hu : (u : 𝔸) = ε⁻¹ • I := by
    simp only [u, Units.val_oneSub, sub_sub_cancel]
  set J : 𝔸 := ε⁻¹ • ((u⁻¹ : 𝔸ˣ) : 𝔸) with hJ_def
  have hIu : I = ε • (u : 𝔸) := by
    rw [hu, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hIJ : I * J = 1 := by
    rw [hIu, hJ_def, smul_mul_smul_comm, mul_inv_cancel₀ hε.ne', one_smul, Units.mul_inv]
  have hJI : J * I = 1 := by
    rw [hIu, hJ_def, smul_mul_smul_comm, inv_mul_cancel₀ hε.ne', one_smul, Units.inv_mul]
  -- Translation of the integral.
  have hshift (t : ℝ) : (∫ s in t..t + ε, M s) = M t * I := by
    have h1 := intervalIntegral.integral_comp_add_left (fun s => M s) (a := 0) (b := ε) t
    simp only [add_zero] at h1
    rw [← h1]
    have h2 : (∫ x in (0 : ℝ)..ε, M (t + x)) = ∫ x in (0 : ℝ)..ε, (M t * M x) :=
      intervalIntegral.integral_congr fun x _ => hadd t x
    rw [h2]
    have h3 := (ContinuousLinearMap.mul ℝ 𝔸 (M t)).intervalIntegral_comp_comm
      (hM.intervalIntegrable (μ := MeasureTheory.volume) 0 ε)
    simpa only [ContinuousLinearMap.mul_apply'] using h3
  -- Differentiability.
  let Fi : ℝ → 𝔸 := fun u => ∫ s in (0 : ℝ)..u, M s
  have hFi (u : ℝ) : HasDerivAt Fi (M u) u :=
    (hM.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hMeq (t : ℝ) : M t = (Fi (t + ε) - Fi t) * J := by
    have h := intervalIntegral.integral_interval_sub_left
      (hM.intervalIntegrable (μ := MeasureTheory.volume) 0 (t + ε))
      (hM.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    change Fi (t + ε) - Fi t = ∫ s in t..t + ε, M s at h
    rw [h, hshift, mul_assoc, hIJ, mul_one]
  set X : 𝔸 := (M ε - 1) * J with hX_def
  have hderiv (t : ℝ) : HasDerivAt M (M t * X) t := by
    have hG : HasDerivAt (fun t => (Fi (t + ε) - Fi t) * J) ((M (t + ε) - M t) * J) t :=
      (((hFi (t + ε)).comp_add_const t ε).sub (hFi t)).mul_const J
    have h1 : HasDerivAt M ((M (t + ε) - M t) * J) t :=
      hG.congr_of_eventuallyEq (Filter.Eventually.of_forall hMeq)
    convert h1 using 1
    rw [hX_def, ← mul_assoc, mul_sub, mul_one, ← hadd]
  -- Commutation.
  have hcommX (Z : 𝔸) (hZ : ∀ s, Commute Z (M s)) : Commute Z X := by
    have hZI : Commute Z I := commute_intervalIntegral hM hZ 0 ε
    have hZJ : Commute Z J := by
      change Z * J = J * Z
      calc Z * J = (J * I) * (Z * J) := by rw [hJI, one_mul]
        _ = J * (Z * I) * J := by rw [hZI.eq]; noncomm_ring
        _ = J * Z * (I * J) := by noncomm_ring
        _ = J * Z := by rw [hIJ, mul_one]
    exact ((hZ ε).sub_right (Commute.one_right Z)).mul_right hZJ
  have hMX (t : ℝ) : Commute (M t) X := by
    apply hcommX
    intro s
    change M t * M s = M s * M t
    rw [← hadd, ← hadd, add_comm]
  refine ⟨X, fun t => ?_, hcommX⟩
  -- `exp (-t X) M t` is constant.
  let h : ℝ → 𝔸 := fun t => exp (t • (-X)) * M t
  have hh (t : ℝ) : HasDerivAt h 0 t := by
    have he := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) t
    have hp := he.mul (hderiv t)
    convert hp using 1
    rw [mul_neg, neg_mul, mul_assoc, ← (hMX t).eq, ← mul_assoc, neg_add_cancel]
  have hconst : h t = h 0 :=
    is_const_of_deriv_eq_zero (fun t => (hh t).differentiableAt) (fun t => (hh t).deriv) t 0
  have h0' : h 0 = 1 := by
    simp only [h, zero_smul, exp_zero, h0, one_mul]
  have hinv : exp (t • X) * exp (t • (-X)) = 1 := by
    rw [smul_neg, ← exp_add_of_commute_real ((Commute.refl X).smul_left t |>.smul_right t |>.neg_right),
      add_neg_cancel, exp_zero]
  calc M t = (exp (t • X) * exp (t • (-X))) * M t := by rw [hinv, one_mul]
    _ = exp (t • X) * h t := by rw [mul_assoc]
    _ = exp (t • X) := by rw [hconst, h0', mul_one]

/-- **Continuous homomorphisms from `ℝ^ι` are exponentials.** A continuous `M : (ι → ℝ) → 𝔸`
with `M 0 = 1` and `M (s + t) = M s * M t` is `t ↦ exp (∑ i, t i • X i)` for pairwise commuting
`X i` that commute with every value of `M`. -/
theorem exists_exp_sum_of_continuous_add_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : (ι → ℝ) → 𝔸) (hM : Continuous M) (h0 : M 0 = 1)
    (hadd : ∀ s t, M (s + t) = M s * M t) :
    ∃ X : ι → 𝔸, (∀ i j, Commute (X i) (X j)) ∧ (∀ t i, Commute (M t) (X i)) ∧
      ∀ t, M t = exp (∑ i, t i • X i) := by
  have hdir (i : ι) : ∃ Y : 𝔸, (∀ s : ℝ, M (Pi.single i s) = exp (s • Y)) ∧
      ∀ Z : 𝔸, (∀ s : ℝ, Commute Z (M (Pi.single i s))) → Commute Z Y := by
    refine exists_exp_of_continuous_add_mul (fun s => M (Pi.single i s))
      (hM.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).continuous) ?_ ?_
    · simp only [Pi.single_zero, h0]
    · intro s t
      simp only [Pi.single_add, hadd]
  choose X hXexp hXcomm using hdir
  have hMcomm (s t : ι → ℝ) : Commute (M s) (M t) := by
    change M s * M t = M t * M s
    rw [← hadd, ← hadd, add_comm]
  have hMX (t : ι → ℝ) (i : ι) : Commute (M t) (X i) :=
    hXcomm i (M t) fun s => hMcomm t _
  refine ⟨X, fun i j => hXcomm j (X i) fun s => (hMX _ i).symm, hMX, fun t => ?_⟩
  have hfin (s : Finset ι) :
      M (∑ i ∈ s, Pi.single i (t i)) = exp (∑ i ∈ s, t i • X i) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, h0, exp_zero]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih, hXexp,
        exp_add_of_commute_real]
      apply Commute.sum_right
      intro i _
      exact ((hXcomm a (X i) fun s => (hMX _ i).symm).symm.smul_left (t a)).smul_right (t i)
  rw [← hfin, Finset.univ_sum_single]

section Eigen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- A joint generalized eigenvector of commuting endomorphisms is a generalized eigenvector of
each linear combination, for the corresponding combination of eigenvalues. -/
theorem mem_maxGenEigenspace_sum {ι : Type*} (X : ι → Module.End ℂ E)
    (hX : ∀ i j, Commute (X i) (X j)) (μ c : ι → ℂ) (s : Finset ι) {v : E}
    (hv : v ∈ ⨅ i, Module.End.maxGenEigenspace (X i) (μ i)) :
    v ∈ Module.End.maxGenEigenspace (∑ i ∈ s, c i • X i) (∑ i ∈ s, c i * μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hcomm : Commute (c a • X a) (∑ i ∈ s, c i • X i) :=
      Commute.sum_right _ _ _ fun i _ => ((hX a i).smul_left _).smul_right _
    have h1 : v ∈ Module.End.maxGenEigenspace (c a • X a) (c a * μ a) :=
      Module.End.genEigenspace_le_smul (X a) (μ a) (c a) ⊤ ((Submodule.mem_iInf _).mp hv a)
    have h2 := Module.End.genEigenspace_inf_le_add (c a • X a) (∑ i ∈ s, c i • X i)
      (c a * μ a) (∑ i ∈ s, c i * μ i) ⊤ ⊤ hcomm ⟨h1, ih⟩
    simpa only [top_add] using h2

/-- **The exponential on a joint generalized eigenspace.** For pairwise commuting `X i` and a
joint generalized eigenvector `v` with eigenvalues `μ i`, the vector `exp (∑ t i • X i) v` is
`exp (∑ t i μ i)` times the finite Taylor sum of the nilpotent part
`N = ∑ t i • (X i - μ i)` applied to `v`, up to the dimension of the space. -/
theorem exp_sum_smul_apply_of_mem {ι : Type*} [Fintype ι] (X : ι → E →L[ℂ] E)
    (hX : ∀ i j, Commute (X i) (X j)) (μ : ι → ℂ) (t : ι → ℝ) {v : E}
    (hv : v ∈ ⨅ i, Module.End.maxGenEigenspace (X i : Module.End ℂ E) (μ i)) :
    exp (∑ i, t i • X i) v = Complex.exp (∑ i, (t i : ℂ) * μ i) •
      ∑ k ∈ Finset.range (Module.finrank ℂ E),
        ((k.factorial : ℂ)⁻¹) • ((∑ i, (t i : ℂ) • (X i - μ i • 1)) ^ k) v := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  set c : ℂ := ∑ i, (t i : ℂ) * μ i with hc
  set N : E →L[ℂ] E := ∑ i, (t i : ℂ) • (X i - μ i • 1) with hN
  have hD : ∑ i, t i • X i = c • (1 : E →L[ℂ] E) + N := by
    simp only [hN, hc, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.sum_smul,
      Complex.coe_smul]
    abel
  -- `N ^ d v = 0`.
  have hNd : (N ^ Module.finrank ℂ E) v = 0 := by
    have hX' : ∀ i j, Commute (X i : Module.End ℂ E) (X j) := by
      intro i j
      change ((X i * X j : E →L[ℂ] E) : Module.End ℂ E) = ((X j * X i : E →L[ℂ] E) :
        Module.End ℂ E)
      rw [(hX i j).eq]
    have hmem := mem_maxGenEigenspace_sum (fun i => (X i : Module.End ℂ E)) hX' μ
      (fun i => (t i : ℂ)) Finset.univ hv
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at hmem
    have hcoe : (∑ i ∈ Finset.univ, (t i : ℂ) • (X i : Module.End ℂ E)) -
        (∑ i ∈ Finset.univ, (t i : ℂ) * μ i) • (1 : Module.End ℂ E) = (N : Module.End ℂ E) := by
      simp only [hN, ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
        ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one, smul_sub,
        Finset.sum_sub_distrib, smul_smul, Finset.sum_smul]
    rw [hcoe, ← ContinuousLinearMap.toLinearMap_pow] at hmem
    exact hmem
  have hzero (k : ℕ) (hk : k ∉ Finset.range (Module.finrank ℂ E)) :
      ((k.factorial : ℂ)⁻¹) • (N ^ k) v = 0 := by
    rw [Finset.mem_range, not_lt] at hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hsplit : (N ^ (Module.finrank ℂ E + m)) v = (N ^ m) ((N ^ Module.finrank ℂ E) v) := by
      rw [add_comm, pow_add]
      rfl
    rw [hsplit, hNd, map_zero, smul_zero]
  have hexpN : exp N v = ∑ k ∈ Finset.range (Module.finrank ℂ E),
      ((k.factorial : ℂ)⁻¹) • (N ^ k) v := by
    have hs := (exp_series_hasSum_exp' (𝕂 := ℂ) N).mapL (ContinuousLinearMap.apply ℂ E v)
    simp only [ContinuousLinearMap.apply_apply, FunLike.coe_smul, Pi.smul_apply]
      at hs
    exact hs.unique (hasSum_sum_of_ne_finset_zero hzero)
  have hexpc : exp (c • (1 : E →L[ℂ] E)) = Complex.exp c • (1 : E →L[ℂ] E) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
      Complex.exp_eq_exp_ℂ, algebraMap_exp_comm]
  rw [hD, exp_add_of_commute_real ((Commute.one_left N).smul_left c), hexpc, smul_mul_assoc,
    one_mul, FunLike.coe_smul, Pi.smul_apply, hexpN]

end Eigen

end Langlands.Analysis.OneParameter
