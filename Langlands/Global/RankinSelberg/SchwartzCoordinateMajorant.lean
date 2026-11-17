import Langlands.Global.RankinSelberg.SchwartzRapidMajorant
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.Basic

/-! # Schwartz majorants preserving coordinate magnitudes -/

noncomputable section
open scoped Classical ContDiff Topology
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzMajorant

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A specified radial smooth bump on a real inner product space. -/
def radialBump (x : H) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace H).toFun 2 x

theorem radialBump_nonneg (x : H) : 0 ≤ radialBump H x :=
  ((ContDiffBumpBase.ofInnerProductSpace H).mem_Icc 2 x).1

theorem radialBump_one (x : H) (hx : ‖x‖ ≤ 1) : radialBump H x = 1 :=
  (ContDiffBumpBase.ofInnerProductSpace H).eq_one 2 one_lt_two x hx

theorem radialBump_eq_of_norm_eq (x y : H) (hxy : ‖x‖ = ‖y‖) :
    radialBump H x = radialBump H y := by
  simp only [radialBump, ContDiffBumpBase.ofInnerProductSpace, hxy]

theorem radialBump_norm_lt_two {x : H} (hx : radialBump H x ≠ 0) : ‖x‖ < 2 := by
  have hx' : x ∈ Function.support
      ((ContDiffBumpBase.ofInnerProductSpace H).toFun 2) := hx
  rw [(ContDiffBumpBase.ofInnerProductSpace H).support 2 one_lt_two] at hx'
  simpa only [Metric.mem_ball, dist_zero_right] using hx'

theorem radialBump_contDiff : ContDiff ℝ ∞ (radialBump H) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact ((ContDiffBumpBase.ofInnerProductSpace H).smooth.contDiffAt
    (prod_mem_nhds (Ioi_mem_nhds one_lt_two) Filter.univ_mem)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)

variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]

/-- The product of radial bumps in all real and complex coordinates. -/
def coordinateBump (x : I → (A → ℝ) × (B → ℂ)) : ℝ :=
  ∏ i, ((∏ a, radialBump ℝ ((x i).1 a)) * ∏ b, radialBump ℂ ((x i).2 b))

theorem coordinateBump_nonneg (x : I → (A → ℝ) × (B → ℂ)) :
    0 ≤ coordinateBump x := by
  exact Finset.prod_nonneg fun i _ => mul_nonneg
    (Finset.prod_nonneg fun a _ => radialBump_nonneg ℝ _)
    (Finset.prod_nonneg fun b _ => radialBump_nonneg ℂ _)

theorem coordinateBump_one (x : I → (A → ℝ) × (B → ℂ)) (hx : ‖x‖ ≤ 1) :
    coordinateBump x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  have hi : ‖x i‖ ≤ 1 := (norm_le_pi_norm x i).trans hx
  have hreal : ∀ a, ‖(x i).1 a‖ ≤ 1 := fun a =>
    (norm_le_pi_norm (x i).1 a).trans ((norm_fst_le (x i)).trans hi)
  have hcomplex : ∀ b, ‖(x i).2 b‖ ≤ 1 := fun b =>
    (norm_le_pi_norm (x i).2 b).trans ((norm_snd_le (x i)).trans hi)
  rw [Finset.prod_eq_one (fun a _ => radialBump_one ℝ _ (hreal a)),
    Finset.prod_eq_one (fun b _ => radialBump_one ℂ _ (hcomplex b)), mul_one]

theorem coordinateBump_contDiff :
    ContDiff ℝ ∞ (coordinateBump (I := I) (A := A) (B := B)) := by
  apply contDiff_prod
  intro i _
  apply ContDiff.mul
  · apply contDiff_prod
    intro a _
    apply (radialBump_contDiff ℝ).comp
    fun_prop
  · apply contDiff_prod
    intro b _
    apply (radialBump_contDiff ℂ).comp
    fun_prop

theorem coordinateBump_norm_le_two {x : I → (A → ℝ) × (B → ℂ)}
    (hx : coordinateBump x ≠ 0) : ‖x‖ ≤ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)
  rw [Prod.norm_def, max_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro a
    exact (radialBump_norm_lt_two ℝ
      (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).1 a (Finset.mem_univ a))).le
  · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro b
    exact (radialBump_norm_lt_two ℂ
      (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).2 b (Finset.mem_univ b))).le

theorem coordinateBump_hasCompactSupport :
    HasCompactSupport (coordinateBump (I := I) (A := A) (B := B)) := by
  apply (isCompact_closedBall (0 : I → (A → ℝ) × (B → ℂ)) 2).of_isClosed_subset
    isClosed_closure
  apply closure_minimal
  · intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      coordinateBump_norm_le_two hx
  · exact Metric.isClosed_closedBall

theorem coordinateBump_eq_of_norm_eq (x y : I → (A → ℝ) × (B → ℂ))
    (hreal : ∀ i a, ‖(x i).1 a‖ = ‖(y i).1 a‖)
    (hcomplex : ∀ i b, ‖(x i).2 b‖ = ‖(y i).2 b‖) :
    coordinateBump x = coordinateBump y := by
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  · exact Finset.prod_congr rfl fun a _ => radialBump_eq_of_norm_eq ℝ _ _ (hreal i a)
  · exact Finset.prod_congr rfl fun b _ => radialBump_eq_of_norm_eq ℂ _ _ (hcomplex i b)

/-- Rapid bounds on a finite row of real and complex coordinates admit a
nonnegative Schwartz majorant depending only on the coordinate magnitudes. -/
theorem exists_coordinate_schwartz_majorant
    {J : Type*} (z : J → I → (A → ℝ) × (B → ℂ)) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j)
    (hrapid : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, (1 + ‖z j‖) ^ N * w j ≤ C) :
    ∃ Φ : SchwartzMap (I → (A → ℝ) × (B → ℂ)) ℝ,
      (∀ x, 0 ≤ Φ x) ∧ (∀ j, w j ≤ Φ (z j)) ∧
      ∀ x y, (∀ i a, ‖(x i).1 a‖ = ‖(y i).1 a‖) →
        (∀ i b, ‖(x i).2 b‖ = ‖(y i).2 b‖) → Φ x = Φ y := by
  let b := coordinateBump_hasCompactSupport.toSchwartzMap
    (coordinateBump_contDiff (I := I) (A := A) (B := B))
  obtain ⟨Φ, hnon, hbound, heq⟩ := exists_nonneg_schwartz_majorant_of_bump b
    coordinateBump_nonneg coordinateBump_one z w hw hrapid
  refine ⟨Φ, hnon, hbound, fun x y hr hc => heq x y fun R _ => ?_⟩
  apply coordinateBump_eq_of_norm_eq
  · intro i a
    change ‖R⁻¹ • (x i).1 a‖ = ‖R⁻¹ • (y i).1 a‖
    rw [norm_smul, norm_smul, hr i a]
  · intro i c
    change ‖R⁻¹ • (x i).2 c‖ = ‖R⁻¹ • (y i).2 c‖
    rw [norm_smul, norm_smul, hc i c]

end Langlands.Global.RankinSelbergGlobal.SchwartzMajorant
