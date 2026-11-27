import Langlands.Global.RankinSelberg.RealDiscreteReciprocalFourier
import Langlands.Representation.Archimedean.RealLeviProducts
import Mathlib.MeasureTheory.Integral.Pi

/-! # Fourier bounds for products of real discrete-series cells -/

noncomputable section

open Complex MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviFourier

open Langlands.Archimedean.RealBlockFourierFinite
open Langlands.Archimedean.RealLeviProducts (prodSpan mem_prodSpan exists_interp)
open RealDiscreteReciprocalFourier

private def highMode (k : ℕ) (j : ℤ) : Prop :=
  ∃ m : ℕ, j = ((k + 1 + 2 * m : ℕ) : ℤ) ∨ j = -((k + 1 + 2 * m : ℕ) : ℤ)

private def modes (k D : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(D : ℤ)) D).filter (highMode k)

/-- Rotation profiles of degree at most `D` with frequencies allowed by discrete weight `k`. -/
def angularSpace (k D : ℕ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (Set.range fun j : modes k D => expMode j.val)

/-- A trigonometric polynomial whose forbidden Fourier coefficients vanish lies in the
finite-dimensional space of discrete angular profiles. -/
theorem mem_angularSpace_of_trigPoly {k D : ℕ} {F : ℝ → ℂ} (hF : F ∈ trigPoly D)
    (hcoeff : ∀ j : ℤ, ¬ (∃ m : ℕ,
      j = ((k + 1 + 2 * m : ℕ) : ℤ) ∨ j = -((k + 1 + 2 * m : ℕ) : ℤ)) → coeff j F = 0) :
    F ∈ angularSpace k D := by
  classical
  let J := modes k D
  let C (j : J) := (2 * (Real.pi : ℂ))⁻¹ * coeff j.val F
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨C, ?_⟩
  ext θ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, C, mul_assoc]
  rw [eq_sum_coeff_of_mem_trigPoly hF θ, Finset.mul_sum]
  rw [Finset.sum_coe_sort J (fun j => (2 * (Real.pi : ℂ))⁻¹ * (coeff j F * expMode j θ))]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hn
  rw [hcoeff j (fun hj' => hn (Finset.mem_filter.mpr ⟨hj, hj'⟩)), zero_mul, mul_zero]

variable {c : ℕ}

private abbrev MultiMode (k D : Fin c → ℕ) := ∀ i, modes (k i) (D i)

private def productMode {k D : Fin c → ℕ} (j : MultiMode k D) (θ : Fin c → ℝ) : ℂ :=
  ∏ i, expMode (j i).val (θ i)

private def modeSpan (k D : Fin c → ℕ) : Submodule ℂ ((Fin c → ℝ) → ℂ) :=
  Submodule.span ℂ (Set.range (productMode (k := k) (D := D)))

private theorem mem_modeSpan {k D : Fin c → ℕ} {F : (Fin c → ℝ) → ℂ}
    (hF : ∀ θ i, (fun v => F (Function.update θ i v)) ∈ angularSpace (k i) (D i)) :
    F ∈ modeSpan k D := by
  classical
  have (i : Fin c) : FiniteDimensional ℂ (angularSpace (k i) (D i)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hprod := mem_prodSpan (fun i => angularSpace (k i) (D i)) F hF
  apply (Submodule.span_le.mpr ?_) hprod
  rintro _ ⟨f, hf, rfl⟩
  have h := fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hf i)
  choose a ha using h
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨fun j => ∏ i, a i (j i), ?_⟩
  ext θ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, productMode]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin c) (j : modes (k i) (D i)) => a i j * expMode j.val (θ i))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    using congrFun (ha i) (θ i)

/-- The inner integrand in entry coordinates, with one real Jacquet variable per
nonzero discrete block. The phases use the sign convention of the real Fourier transform. -/
def angularIntegrand (k : Fin c → ℕ) (F : (Fin c → ℝ) → ℂ) (s x : Fin c → ℝ) : ℂ :=
  F (fun i => Real.arctan (x i)) *
    ∏ i, ((Real.sqrt (1 + x i ^ 2) : ℝ) : ℂ)⁻¹ ^ (k i + 1) *
      Complex.exp (↑(-2 * Real.pi * x i * s i) * I)

private theorem angularIntegrand_productMode {k D : Fin c → ℕ} (j : MultiMode k D)
    (s x : Fin c → ℝ) :
    angularIntegrand k (productMode j) s x =
      ∏ i, Complex.exp (↑(-2 * Real.pi * x i * s i) * I) * angularKernel (k i) (j i).val (x i) := by
  rw [angularIntegrand, productMode, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  unfold angularKernel
  ring

private theorem integrable_fourierKernel {f : ℝ → ℂ} (hf : Integrable f) (s : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * s) * I) * f x) := by
  simpa only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, Real.inner_apply,
    mul_neg, neg_mul, mul_assoc] using (Real.fourierIntegral_convergent_iff (E := ℂ) (μ := volume) s).mpr hf

private theorem bound_productMode {k D : Fin c → ℕ} (hk : ∀ i, k i ≠ 0) (j : MultiMode k D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Fin c → ℝ, Integrable (angularIntegrand k (productMode j) s) ∧
      ‖∫ x, angularIntegrand k (productMode j) s x‖ ≤ C * ∏ i, |s i| ^ ((k i : ℝ) / 2) := by
  classical
  have hmode (i : Fin c) : highMode (k i) (j i).val :=
    (Finset.mem_filter.mp (j i).property).2
  have h i := realDiscreteAngularFourierBound (k i) (hk i) (j i).val
    (hmode i) ((k i : ℝ) / 2) (by positivity) (half_le_self (Nat.cast_nonneg _))
  choose B hB hEst using fun i => (h i).2
  refine ⟨∏ i, B i, Finset.prod_nonneg fun i _ => hB i, fun s => ?_⟩
  let g (i : Fin c) (x : ℝ) := Complex.exp (↑(-2 * Real.pi * x * s i) * I) *
    angularKernel (k i) (j i).val x
  have hInt (i : Fin c) : Integrable (g i) := integrable_fourierKernel (h i).1 (s i)
  have hEq : angularIntegrand k (productMode j) s = fun x => ∏ i, g i (x i) :=
    funext (angularIntegrand_productMode j s)
  rw [hEq]
  refine ⟨Integrable.fintype_prod hInt, ?_⟩
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod g, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  simpa only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul, g] using hEst i (s i)

private theorem bound_of_mem_modeSpan {k D : Fin c → ℕ} (hk : ∀ i, k i ≠ 0)
    {F : (Fin c → ℝ) → ℂ} (hF : F ∈ modeSpan k D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : Fin c → ℝ, Integrable (angularIntegrand k F s) ∧
      ‖∫ x, angularIntegrand k F s x‖ ≤ C * ∏ i, |s i| ^ ((k i : ℝ) / 2) := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hF
  choose B hB hEst using bound_productMode hk (D := D)
  refine ⟨∑ j, ‖a j‖ * B j, Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hB j), ?_⟩
  intro s
  have hf : angularIntegrand k F s = fun x => ∑ j, a j * angularIntegrand k (productMode j) s x := by
    funext x
    unfold angularIntegrand
    rw [← ha]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, mul_assoc]
  rw [hf]
  have hi (j : MultiMode k D) := (hEst j s).1.const_mul (a j)
  refine ⟨integrable_finsetSum _ fun j _ => hi j, ?_⟩
  rw [integral_finsetSum _ fun j _ => hi j]
  simp_rw [integral_const_mul]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => by
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hEst j s).2 (norm_nonneg _)

/-- A bounded compact profile with only allowed discrete modes in each coordinate
has a product of Fourier power gains in the inner Jacquet variables. -/
def RealDiscreteLeviFourierBoundStatement : Prop :=
  ∀ (c : ℕ) (k D : Fin c → ℕ), (∀ i, k i ≠ 0) → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (F : (Fin c → ℝ) → ℂ) (R : ℝ), (∀ θ, ‖F θ‖ ≤ R) →
      (∀ θ i, (fun v => F (Function.update θ i v)) ∈ angularSpace (k i) (D i)) →
      ∀ s : Fin c → ℝ, Integrable (angularIntegrand k F s) ∧
        ‖∫ x, angularIntegrand k F s x‖ ≤ C * R * ∏ i, |s i| ^ ((k i : ℝ) / 2)

theorem realDiscreteLeviFourierBound : RealDiscreteLeviFourierBoundStatement := by
  classical
  intro c k D hk
  let W := modeSpan k D
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  obtain ⟨ι, _, θ, f, hf, hInterp⟩ := exists_interp W
  choose B hB hEst using fun j => bound_of_mem_modeSpan hk (hf j)
  refine ⟨∑ j, B j, Finset.sum_nonneg fun j _ => hB j, fun F R hR hF s => ?_⟩
  have hg : angularIntegrand k F s = fun x => ∑ j, F (θ j) * angularIntegrand k (f j) s x := by
    funext x
    unfold angularIntegrand
    conv_lhs => rw [hInterp F (mem_modeSpan hF)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [hg]
  have hi (j : ι) := (hEst j s).1.const_mul (F (θ j))
  refine ⟨integrable_finsetSum _ fun j _ => hi j, ?_⟩
  rw [integral_finsetSum _ fun j _ => hi j]
  simp_rw [integral_const_mul]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => by
    rw [norm_mul, mul_comm (B j) R, mul_assoc]
    exact mul_le_mul (hR (θ j)) (hEst j s).2 (norm_nonneg _)
      ((norm_nonneg _).trans (hR (θ j)))

end Langlands.Global.RankinSelbergGlobal.RealDiscreteLeviFourier
