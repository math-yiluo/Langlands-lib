import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Langlands.Representation.Archimedean.RealBlockRotation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

/-! # Probability Haar integration on the real orthogonal groups in ranks one and two -/

noncomputable section

set_option autoImplicit false

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator Topology

namespace Langlands.Archimedean.RealSmallOrthogonalHaar

open RealBlockRotation

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

/-- The opposite sign on the one-dimensional orthogonal group. -/
abbrev signOne : K 1 := signReflection 1 0

/-- The first-coordinate reflection on the two-dimensional orthogonal group. -/
abbrev reflectTwo : K 2 := signReflection 2 0

/-- The existing block rotation as an element of the two-dimensional orthogonal group. -/
def rotation (θ : ℝ) : K 2 :=
  ⟨(blockRotation 2 0 θ : M 2), blockRotation_mem_unitaryCompact 2 0 θ⟩

@[simp]
theorem toUnits_rotation (θ : ℝ) :
    Unitary.toUnits (rotation θ) = blockRotation 2 0 θ := by
  apply Units.ext
  rfl

theorem continuous_rotation : Continuous rotation :=
  Continuous.subtype_mk (Units.continuous_val.comp (continuous_blockRotation 2 0)) _

theorem rotation_add (θ η : ℝ) : rotation (θ + η) = rotation θ * rotation η :=
  Subtype.ext (congrArg Units.val (blockRotation_add 2 0 θ η))

theorem rotation_periodic : Function.Periodic rotation (2 * Real.pi) :=
  fun θ => Subtype.ext (congrArg Units.val (blockRotation_add_two_pi (by decide : 0 + 1 < 2) θ))

theorem rotation_val (θ : ℝ) :
    (rotation θ : M 2) = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  ext i j
  change (blockRotation 2 0 θ : M 2) i j = _
  rw [blockRotation_apply (by decide : 0 + 1 < 2)]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]

private theorem reflect_rotation (θ : ℝ) : reflectTwo * rotation θ = rotation (-θ) * reflectTwo := by
  have h : reflectTwo * rotation θ * reflectTwo = rotation (-θ) :=
    Subtype.ext (congrArg Units.val
      (signReflection_mul_blockRotation_mul_of_mem (by decide : 0 + 1 < 2)
        (0 : Fin 2) (.inl rfl) θ))
  calc
    _ = (reflectTwo * rotation θ * reflectTwo) * reflectTwo := by
      rw [mul_assoc (reflectTwo * rotation θ), signReflection_mul_self, mul_one]
    _ = _ := by rw [h]

/-- The orthogonal group in dimension one consists of the two signs. -/
theorem orthogonal_one_cases (k : K 1) : k = 1 ∨ k = signOne := by
  have hk := (mem_orthogonalGroup_iff (Fin 1) ℝ).mp k.2
  have he := congrArg (fun A : M 1 => A 0 0) hk
  have hsq : k.val 0 0 * k.val 0 0 = 1 := by
    simpa [Matrix.mul_apply] using he
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    apply Subtype.ext
    ext i j
    rw [Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1)]
    simpa using h
  · right
    apply Subtype.ext
    ext i j
    rw [Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1)]
    simpa [signReflection_val] using h

private theorem det_reflectTwo : (reflectTwo : M 2).det = -1 := by
  change (diagonal fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 1).det = -1
  simp

private theorem exists_rotation_of_det_one (k : K 2) (hk : k.val.det = 1) :
    ∃ θ, k = rotation θ := by
  have hu : k.val ∈ specialOrthogonalGroup (Fin 2) ℝ :=
    mem_specialOrthogonalGroup_iff.mpr ⟨k.2, hk⟩
  obtain ⟨hdiag, hskew, hsq⟩ := mem_specialOrthogonalGroup_fin_two_iff.mp hu
  let z : ℂ := ⟨k.val 0 0, k.val 1 0⟩
  have hnormsq : ‖z‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq]
    simpa [z, hskew] using hsq
  have hnorm : ‖z‖ = 1 := (sq_eq_one_iff.mp hnormsq).resolve_right (by
    intro hn
    linarith [norm_nonneg z])
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hnorm
  have hc : Real.cos z.arg = k.val 0 0 := by rw [Complex.cos_arg hz, hnorm, div_one]
  have hs : Real.sin z.arg = k.val 1 0 := by rw [Complex.sin_arg, hnorm, div_one]
  refine ⟨z.arg, Subtype.ext ?_⟩
  rw [rotation_val, hc, hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hdiag, hskew]

/-- Every two-dimensional orthogonal matrix is a rotation or a rotation followed
by the first-coordinate reflection. -/
theorem orthogonal_two_cases (k : K 2) :
    ∃ θ, k = rotation θ ∨ k = rotation θ * reflectTwo := by
  have hk := (mem_orthogonalGroup_iff (Fin 2) ℝ).mp k.2
  have hsq : k.val.det * k.val.det = 1 := by
    simpa only [det_mul, det_transpose, det_one] using congrArg Matrix.det hk
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · obtain ⟨θ, he⟩ := exists_rotation_of_det_one k h
    exact ⟨θ, .inl he⟩
  · have he : (k * reflectTwo : K 2).val.det = 1 := by
      change (k.val * (reflectTwo : M 2)).det = 1
      rw [det_mul, h, det_reflectTwo]
      norm_num
    obtain ⟨θ, hr⟩ := exists_rotation_of_det_one (k * reflectTwo) he
    exact ⟨θ, .inr (by rw [← hr, mul_assoc, signReflection_mul_self, mul_one])⟩

/-- Haar probability on the one-dimensional orthogonal group averages the two signs. -/
theorem integral_orthogonal_one (μ : Measure (K 1)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : C(K 1, ℂ)) :
    (∫ k, f k ∂μ) = (f 1 + f signOne) / 2 := by
  have hconst (k : K 1) : f k + f (signOne * k) = f 1 + f signOne := by
    rcases orthogonal_one_cases k with rfl | rfl
    · rw [mul_one]
    · rw [signReflection_mul_self, add_comm]
  have hf : Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (fun k => f (signOne * k)) μ :=
    (f.continuous.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi := integral_mul_left_eq_self (μ := μ) (fun k => f k) signOne
  calc
    _ = (∫ k, (f k + f (signOne * k)) ∂μ) / 2 := by rw [integral_add hf hg, hi]; ring
    _ = _ := by simp only [hconst, integral_const, probReal_univ, one_smul]

private def angleIntegral (f : C(K 2, ℂ)) (w k : K 2) : ℂ :=
  ∫ θ in 0..2 * Real.pi, f (rotation θ * w * k)

private theorem continuous_angleIntegrand (f : C(K 2, ℂ)) (w : K 2) :
    Continuous (fun p : K 2 × ℝ => f (rotation p.2 * w * p.1)) :=
  f.continuous.comp (((continuous_rotation.comp continuous_snd).mul continuous_const).mul continuous_fst)

private theorem continuous_angleIntegral (f : C(K 2, ℂ)) (w : K 2) :
    Continuous (angleIntegral f w) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_angleIntegrand f w) _ _

private theorem angle_shift (f : C(K 2, ℂ)) (w : K 2) (a : ℝ) :
    (∫ θ in 0..2 * Real.pi, f (rotation (θ + a) * w)) = angleIntegral f w 1 := by
  let g (θ : ℝ) := f (rotation θ * w)
  have hg : Function.Periodic g (2 * Real.pi) := by
    intro θ
    dsimp [g]
    rw [rotation_periodic θ]
  unfold angleIntegral
  simp only [mul_one]
  change (∫ θ in 0..2 * Real.pi, g (θ + a)) = ∫ θ in 0..2 * Real.pi, g θ
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (2 * Real.pi) a] using hg.intervalIntegral_add_eq a 0

private theorem angleIntegral_sum_const (f : C(K 2, ℂ)) (k : K 2) :
    angleIntegral f 1 k + angleIntegral f reflectTwo k =
      angleIntegral f 1 1 + angleIntegral f reflectTwo 1 := by
  obtain ⟨a, ha | ha⟩ := orthogonal_two_cases k
  · rw [ha]
    have h₁ (θ : ℝ) : rotation θ * 1 * rotation a = rotation (θ + a) * 1 := by
      rw [mul_one, mul_one, rotation_add]
    have h₂ (θ : ℝ) : rotation θ * reflectTwo * rotation a =
        rotation (θ + -a) * reflectTwo := by
      rw [mul_assoc, reflect_rotation, ← mul_assoc, ← rotation_add]
    conv_lhs => rw [angleIntegral, angleIntegral]
    simp_rw [h₁, h₂, angle_shift]
  · rw [ha]
    have h₁ (θ : ℝ) : rotation θ * 1 * (rotation a * reflectTwo) =
        rotation (θ + a) * reflectTwo := by rw [mul_one, ← mul_assoc, ← rotation_add]
    have h₂ (θ : ℝ) : rotation θ * reflectTwo * (rotation a * reflectTwo) =
        rotation (θ + -a) * 1 := by
      rw [← mul_assoc, mul_assoc (rotation θ), reflect_rotation, ← mul_assoc (rotation θ),
        mul_assoc (rotation θ * rotation (-a)), signReflection_mul_self, rotation_add]
    conv_lhs => rw [angleIntegral, angleIntegral]
    simp_rw [h₁, h₂, angle_shift]
    exact add_comm _ _

private theorem integral_angleIntegral (μ : Measure (K 2)) [μ.IsHaarMeasure]
    (f : C(K 2, ℂ)) (w : K 2) :
    (∫ k, angleIntegral f w k ∂μ) = (2 * (Real.pi : ℂ)) * ∫ k, f k ∂μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have : IsFiniteMeasure ν := by
    rw [isFiniteMeasure_restrict]
    exact measure_Ioc_lt_top.ne
  let F (p : K 2 × ℝ) := f (rotation p.2 * w * p.1)
  have hF : Integrable F (μ.prod ν) := Integrable.of_bound
    (continuous_angleIntegrand f w).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall fun p => f.norm_coe_le_norm (rotation p.2 * w * p.1))
  simp only [angleIntegral, intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * Real.pi)]
  change (∫ k, (∫ θ, F (k, θ) ∂ν) ∂μ) = _
  rw [integral_integral_swap hF]
  have htr (θ : ℝ) : (∫ k, F (k, θ) ∂μ) = ∫ k, f k ∂μ :=
    integral_mul_left_eq_self (μ := μ) (fun k => f k) (rotation θ * w)
  simp_rw [htr]
  rw [integral_const]
  change (volume.restrict (Set.Ioc 0 (2 * Real.pi))).real Set.univ • _ = _
  rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc, sub_zero, max_eq_left (by positivity),
    Complex.real_smul]
  push_cast
  ring

/-- Haar probability in dimension two is the half-sum of the two normalized angle integrals. -/
theorem integral_orthogonal_two (μ : Measure (K 2)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : C(K 2, ℂ)) :
    (∫ k, f k ∂μ) =
      ((∫ θ in 0..2 * Real.pi, f (rotation θ)) +
        (∫ θ in 0..2 * Real.pi, f (rotation θ * reflectTwo))) / (4 * (Real.pi : ℂ)) := by
  have hf : ∀ w, Integrable (angleIntegral f w) μ := fun w =>
    (continuous_angleIntegral f w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h : (4 * (Real.pi : ℂ)) * (∫ k, f k ∂μ) =
      angleIntegral f 1 1 + angleIntegral f reflectTwo 1 := calc
    _ = (∫ k, (angleIntegral f 1 k + angleIntegral f reflectTwo k) ∂μ) := by
      rw [integral_add (hf 1) (hf reflectTwo), integral_angleIntegral, integral_angleIntegral]
      ring
    _ = _ := by simp only [angleIntegral_sum_const, integral_const, probReal_univ, one_smul]
  have hπ : (4 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  apply (eq_div_iff hπ).2
  rw [mul_comm]
  simpa only [angleIntegral, mul_one] using h

/-- The Haar probability integration formulas on the one- and two-dimensional orthogonal groups. -/
def RealSmallOrthogonalHaarStatement : Prop :=
  (∀ (μ : Measure (K 1)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (f : C(K 1, ℂ)),
    (∫ k, f k ∂μ) = (f 1 + f signOne) / 2) ∧
  (∀ (μ : Measure (K 2)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (f : C(K 2, ℂ)),
    (∫ k, f k ∂μ) =
      ((∫ θ in 0..2 * Real.pi, f (rotation θ)) +
        (∫ θ in 0..2 * Real.pi, f (rotation θ * reflectTwo))) / (4 * (Real.pi : ℂ)))

theorem realSmallOrthogonalHaar : RealSmallOrthogonalHaarStatement :=
  ⟨integral_orthogonal_one, integral_orthogonal_two⟩

end Langlands.Archimedean.RealSmallOrthogonalHaar
