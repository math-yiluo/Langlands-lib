import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Analysis.ConeFourierBoundary

/-! # Polynomial Fourier boundary values of the regularized pairing -/

noncomputable section

open Filter MeasureTheory Set
open scoped Classical Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Analysis

variable {ι : Type*} [Fintype ι]

/-- Translate the open orthant oriented by `d` by `-b`. -/
def translatedOrientedOrthant (d b : ι → ℝ) : Set (ι → ℝ) :=
  (fun x => x + b) ⁻¹' orientedOrthant d

private theorem halfLine_polynomialLaplace {z : ℂ} (hz : z.re ≠ 0) (k : ℕ) :
    let s : Set ℝ := if 0 < z.re then Ioi 0 else Iio 0
    let f (x : ℝ) := (-(x : ℂ)) ^ k * Complex.exp (-z * (x : ℂ))
    IntegrableOn f s ∧ (∫ x in s, f x) = (if 0 < z.re then 1 else -1) * orthantFactor k z := by
  dsimp only
  by_cases hp : 0 < z.re
  · let g (x : ℝ) := (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))
    have hg : IntegrableOn g (Iic 0) := integrableOn_Iic_pow_mul_cexp hp k
    have hneg : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ), hneg.integrableOn_map_iff,
      neg_preimage, neg_Iic, neg_zero, integrableOn_Ici_iff_integrableOn_Ioi] at hg
    have hfun (x : ℝ) : (-(x : ℂ)) ^ k * Complex.exp (-z * (x : ℂ)) = g (-x) := by
      simp only [g, Complex.ofReal_neg, mul_neg, neg_mul]
    simp_rw [ite_eq_left hp, hfun, integral_comp_neg_Ioi, neg_zero, one_mul]
    exact ⟨hg, integral_Iic_pow_mul_cexp hp k⟩
  · have hn : 0 < (-z).re := by
      rw [Complex.neg_re]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hz)
    have hfun (x : ℝ) : (-(x : ℂ)) ^ k * Complex.exp (-z * (x : ℂ)) =
        (-1 : ℂ) ^ k * ((x : ℂ) ^ k * Complex.exp (-z * (x : ℂ))) := by
      rw [← neg_one_mul (x : ℂ), mul_pow, mul_assoc]
    simp_rw [ite_eq_right hp, hfun]
    refine ⟨IntegrableOn.mono_set ((integrableOn_Iic_pow_mul_cexp hn k).const_mul _)
      Iio_subset_Iic_self, ?_⟩
    rw [integral_const_mul, ← integral_Iic_eq_integral_Iio, integral_Iic_pow_mul_cexp hn k]
    have hpow : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    have hz' : z ≠ 0 := fun h => hz (by rw [h]; simp)
    calc
      _ = (k.factorial : ℂ) / (-z) ^ (k + 1) := by
        rw [← mul_div_assoc, ← mul_assoc, hpow, one_mul]
      _ = (-1 : ℂ) * orthantFactor k z := by
        rw [orthantFactor, neg_pow, pow_succ (-1 : ℂ)]
        calc
          _ = ((-1 : ℂ) ^ k * (-1) ^ k) * (k.factorial : ℂ) /
              (((-1 : ℂ) ^ k * -1) * z ^ (k + 1)) := by rw [hpow, one_mul]
          _ = _ := by field_simp

private theorem orthant_polynomialLaplace {d : ι → ℝ} {z : ι → ℂ}
    (hz : ∀ i, (z i).re ≠ 0) (hs : ∀ i, 0 < (z i).re ↔ 0 < d i) (P : MvPolynomial ι ℂ) :
    let f (x : ι → ℝ) := Complex.exp (∑ i, -z i * (x i : ℂ)) *
      MvPolynomial.eval (fun i => -(x i : ℂ)) P
    IntegrableOn f (orientedOrthant d) ∧
      (∫ x in orientedOrthant d, f x) = orthantSign d * negativeOrthantRegularizedIntegral z P := by
  dsimp only
  let H (i : ι) : Set ℝ := if 0 < d i then Ioi 0 else Iio 0
  have hH : orientedOrthant d = univ.pi H := rfl
  have hterm (k : ι →₀ ℕ) (i : ι) := halfLine_polynomialLaplace (hz i) (k i)
  simp only [hs] at hterm
  have hsum (x : ι → ℝ) : Complex.exp (∑ i, -z i * (x i : ℂ)) *
      MvPolynomial.eval (fun i => -(x i : ℂ)) P =
      ∑ k ∈ P.support, P.coeff k * ∏ i, (-(x i : ℂ)) ^ k i * Complex.exp (-z i * (x i : ℂ)) := by
    rw [MvPolynomial.eval_eq', Finset.mul_sum, Complex.exp_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hsum]
  rw [IntegrableOn, hH, volume_pi, Measure.restrict_pi_pi]
  have hI (k : ι →₀ ℕ) : Integrable
      (fun x : ι → ℝ => P.coeff k * ∏ i, (-(x i : ℂ)) ^ k i * Complex.exp (-z i * (x i : ℂ)))
      (Measure.pi fun i => (volume : Measure ℝ).restrict (H i)) :=
    (Integrable.fintype_prod fun i => (hterm k i).1).const_mul _
  refine ⟨integrable_finsetSum _ (fun k _ => hI k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hI k), negativeOrthantRegularizedIntegral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_fintype_prod_eq_prod (fun i (t : ℝ) =>
    (-(t : ℂ)) ^ k i * Complex.exp (-z i * (t : ℂ)))]
  rw [Finset.prod_congr rfl (fun i _ => (hterm k i).2), Finset.prod_mul_distrib, orthantSign]
  ring

omit [Fintype ι] in
private theorem eval_polynomialShift_neg (b x : ι → ℝ) (P : MvPolynomial ι ℂ) :
    MvPolynomial.eval (fun i => -(x i : ℂ)) (polynomialShift b P) =
      MvPolynomial.eval (fun i => -((x - b) i : ℂ)) P := by
  simp only [polynomialShift, ← MvPolynomial.aeval_eq_eval, ← AlgHom.comp_apply,
    MvPolynomial.comp_aeval, map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Algebra.algebraMap_self_apply, Pi.sub_apply, Complex.ofReal_sub, neg_sub, add_comm]
  congr 1

/-- The polynomial regularized integral with a translated vertex is the signed Laplace
integral over the corresponding reflected, oriented and translated orthant. -/
theorem translatedOrthant_polynomialLaplace {d : ι → ℝ} {z : ι → ℂ}
    (hz : ∀ i, (z i).re ≠ 0) (hs : ∀ i, 0 < (z i).re ↔ 0 < d i)
    (b : ι → ℝ) (P : MvPolynomial ι ℂ) :
    let f (x : ι → ℝ) := Complex.exp (∑ i, -z i * (x i : ℂ)) *
      MvPolynomial.eval (fun i => -(x i : ℂ)) P
    IntegrableOn f (translatedOrientedOrthant d b) ∧
      orthantSign d * (Complex.exp (∑ i, (b i : ℂ) * z i) *
        negativeOrthantRegularizedIntegral z (polynomialShift b P)) =
        ∫ x in translatedOrientedOrthant d b, f x := by
  dsimp only
  let f (x : ι → ℝ) := Complex.exp (∑ i, -z i * (x i : ℂ)) *
    MvPolynomial.eval (fun i => -(x i : ℂ)) P
  let c := Complex.exp (∑ i, (b i : ℂ) * z i)
  have hfun (x : ι → ℝ) : f (x - b) = c *
      (Complex.exp (∑ i, -z i * (x i : ℂ)) *
        MvPolynomial.eval (fun i => -(x i : ℂ)) (polynomialShift b P)) := by
    dsimp only [f]
    rw [eval_polynomialShift_neg, ← mul_assoc, ← Complex.exp_add, ← Finset.sum_add_distrib]
    refine congrArg (fun s => Complex.exp s * _) (Finset.sum_congr rfl (fun i _ => ?_))
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    ring
  let e : (ι → ℝ) ≃ₜ (ι → ℝ) := Homeomorph.addRight (-b)
  have he : MeasurePreserving e volume volume := measurePreserving_add_right volume (-b)
  have hpre : e ⁻¹' translatedOrientedOrthant d b = orientedOrthant d := by
    ext x
    change ((x + -b) + b) ∈ orientedOrthant d ↔ x ∈ orientedOrthant d
    rw [add_assoc, neg_add_cancel, add_zero]
  have hcoe (x : ι → ℝ) : e x = x - b := sub_eq_add_neg x b |>.symm
  have h := orthant_polynomialLaplace hz hs (polynomialShift b P)
  change IntegrableOn f (translatedOrientedOrthant d b) ∧ _
  refine ⟨?_, ?_⟩
  · rw [← he.map_eq, e.isClosedEmbedding.measurableEmbedding.integrableOn_map_iff, hpre]
    change IntegrableOn (fun x => f (e x)) (orientedOrthant d)
    simp_rw [hcoe, hfun]
    exact h.1.const_mul c
  · rw [← he.setIntegral_preimage_emb e.isClosedEmbedding.measurableEmbedding f _, hpre]
    simp_rw [hcoe, hfun, integral_const_mul, h.2]
    ring

private def coneDot (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

private def conePhase (x y : ι → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((-coneDot x y : ℝ) : ℂ))

/-- The `i`th coroot evaluation along the real displacement `t d` from the imaginary axis. -/
def displacedOrthantParameter (d : ι → ℝ) (t : ℝ) (y : ι → ℝ) (i : ι) : ℂ :=
  ((t * d i : ℝ) : ℂ) + Complex.I * (y i : ℂ)

omit [Fintype ι] in
private theorem displacedOrthantParameter_re (d : ι → ℝ) (t : ℝ) (y : ι → ℝ) (i : ι) :
    (displacedOrthantParameter d t y i).re = t * d i := by
  simp [displacedOrthantParameter, Complex.mul_re]

private theorem exp_displacedOrthantParameter (d : ι → ℝ) (t : ℝ) (x y : ι → ℝ) :
    Complex.exp (∑ i, -displacedOrthantParameter d t y i * (x i : ℂ)) =
      (Real.exp (-(t * coneDot d x)) : ℂ) * conePhase x y := by
  rw [Complex.ofReal_exp, conePhase, ← Complex.exp_add]
  congr 1
  simp only [displacedOrthantParameter, coneDot]
  push_cast
  rw [← neg_mul, mul_neg, ← neg_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem norm_conePhase (x y : ι → ℝ) : ‖conePhase x y‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

/-- An oriented orthant component after translating its vertex, with the polynomial shifted
as in `StandardParabolicFamily.UnitaryPairingExpansion.regularizedConeIntegral`. -/
def regularizedOrthantTerm (b : ι → ℝ) (P : MvPolynomial ι ℂ) (z : ι → ℂ) : ℂ :=
  Complex.exp (∑ i, (b i : ℂ) * z i) * negativeOrthantRegularizedIntegral z (polynomialShift b P)

/-- The Fourier test on the reflected spatial coordinate, multiplied by the reflected
polynomial. -/
def orthantPolynomialTest (ν : Measure (ι → ℝ)) (f : (ι → ℝ) → ℂ)
    (P : MvPolynomial ι ℂ) (x : ι → ℝ) : ℂ :=
  MvPolynomial.eval (fun i => -(x i : ℂ)) P * orthantFourierTest ν f x

private theorem regularizedOrthantTerm_integral (d b : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (P : MvPolynomial ι ℂ) {ν : Measure (ι → ℝ)} [SFinite ν] {f : (ι → ℝ) → ℂ}
    (hf : Integrable f ν) {t : ℝ} (ht : 0 < t) :
    orthantSign d * (∫ y, regularizedOrthantTerm b P (displacedOrthantParameter d t y) * f y ∂ν) =
      ∫ x in translatedOrientedOrthant d b,
        Real.exp (-(t * coneDot d x)) • orthantPolynomialTest ν f P x := by
  let μ : Measure (ι → ℝ) := volume.restrict (translatedOrientedOrthant d b)
  let c (x : ι → ℝ) := (Real.exp (-(t * coneDot d x)) : ℂ)
  let p (x : ι → ℝ) := MvPolynomial.eval (fun i => -(x i : ℂ)) P
  have hLaplace (y : ι → ℝ) := translatedOrthant_polynomialLaplace
    (d := d) (z := displacedOrthantParameter d t y)
    (fun i => by rw [displacedOrthantParameter_re]; exact mul_ne_zero ht.ne' (hd i))
    (fun i => by rw [displacedOrthantParameter_re]; exact mul_pos_iff_of_pos_left ht) b P
  have hc : Integrable (fun x => c x * p x) μ := by
    have hOne (x : ι → ℝ) : conePhase x 0 = 1 := by simp [conePhase, coneDot]
    simpa only [IntegrableOn, c, p, μ, exp_displacedOrthantParameter, hOne, mul_one]
      using (hLaplace 0).1
  let g (x y : ι → ℝ) : ℂ := (c x * p x) * (conePhase x y * f y)
  have hphase : Continuous (fun w : (ι → ℝ) × (ι → ℝ) => conePhase w.1 w.2) := by
    unfold conePhase coneDot
    fun_prop
  have hg : Integrable (Function.uncurry g) (μ.prod ν) := by
    refine (hc.mul_prod hf).mono
      (hc.aestronglyMeasurable.comp_fst.mul
        (hphase.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd)) ?_
    exact ae_of_all _ (fun w => by
      change ‖(c w.1 * p w.1) * (conePhase w.1 w.2 * f w.2)‖ ≤ ‖(c w.1 * p w.1) * f w.2‖
      simp [norm_conePhase])
  have hExp (x y : ι → ℝ) :
      Complex.exp (∑ i, -displacedOrthantParameter d t y i * (x i : ℂ)) * p x =
        (c x * p x) * conePhase x y := by
    rw [exp_displacedOrthantParameter]
    exact mul_right_comm (c x) (conePhase x y) (p x)
  calc
    _ = ∫ y, (∫ x, g x y ∂μ) ∂ν := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change orthantSign d * (regularizedOrthantTerm b P (displacedOrthantParameter d t y) * f y) =
          ∫ x, g x y ∂μ
        simp_rw [g, ← mul_assoc, ← hExp, integral_mul_const]
        change orthantSign d * regularizedOrthantTerm b P (displacedOrthantParameter d t y) * f y =
          (∫ x, Complex.exp (∑ i, -displacedOrthantParameter d t y i * (x i : ℂ)) * p x ∂μ) * f y
        rw [← (hLaplace y).2]
        rfl
    _ = ∫ x, (∫ y, g x y ∂ν) ∂μ := (integral_integral_swap hg).symm
    _ = _ := by
      simp_rw [g, integral_const_mul, orthantPolynomialTest, Complex.real_smul, mul_assoc]
      rfl

omit [Fintype ι] in
private theorem mem_translatedOrientedOrthant {d b x : ι → ℝ} (hd : ∀ i, d i ≠ 0) :
    x ∈ translatedOrientedOrthant d b ↔ ∀ i, 0 < (x i + b i) * d i := by
  change (∀ i ∈ univ, (x + b) i ∈ (if 0 < d i then Ioi 0 else Iio 0)) ↔ _
  simp only [Set.mem_univ, true_implies, Pi.add_apply]
  refine forall_congr' fun i => ?_
  by_cases hp : 0 < d i
  · simp [ite_eq_left hp, mul_pos_iff_of_pos_right hp]
  · have hn : d i < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hd i)
    rw [ite_eq_right hp, mem_Iio]
    exact ⟨fun h => mul_pos_of_neg_of_neg h hn,
      fun h => ((mul_pos_iff.mp h).resolve_left fun h' => hp h'.2).1⟩

/-- With the orientation sign, the tested displaced polynomial term converges to the
polynomial Fourier integral on the translated oriented orthant. The spectral test is
integrable for the supplied s-finite measure and its polynomial Fourier test is integrable
on that orthant for product Lebesgue measure. -/
def RegularizedOrthantFourierBoundaryStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] (d b : ι → ℝ) (P : MvPolynomial ι ℂ)
    (ν : Measure (ι → ℝ)) [SFinite ν] (f : (ι → ℝ) → ℂ),
    (∀ i, d i ≠ 0) → Integrable f ν →
    IntegrableOn (orthantPolynomialTest ν f P) (translatedOrientedOrthant d b) →
    Tendsto (fun t : ℝ => orthantSign d *
      (∫ y, regularizedOrthantTerm b P (displacedOrthantParameter d t y) * f y ∂ν))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in translatedOrientedOrthant d b, orthantPolynomialTest ν f P x))

theorem regularizedOrthantFourierBoundary : RegularizedOrthantFourierBoundaryStatement := by
  intro ι _ d b P ν _ f hd hf hFourier
  let S := translatedOrientedOrthant d b
  let μ : Measure (ι → ℝ) := volume.restrict S
  have hS : MeasurableSet S := by
    have hEq : S = ⋂ i, {x | 0 < (x i + b i) * d i} := by
      ext x
      simp only [S, mem_translatedOrientedOrthant hd, mem_iInter, mem_ofPred_eq]
    rw [hEq]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (((measurable_pi_apply i).add_const _).mul_const _)
  have hdot (x : ι → ℝ) : coneDot d x + coneDot d b = ∑ i, (x i + b i) * d i := by
    rw [coneDot, coneDot, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hNonneg : ∀ᵐ x ∂μ, 0 ≤ coneDot d x + coneDot d b :=
    (ae_restrict_mem hS).mono fun x hx => by
      rw [hdot]
      exact Finset.sum_nonneg fun i _ => ((mem_translatedOrientedOrthant hd).mp hx i).le
  have hMeas : Measurable (fun x : ι → ℝ => coneDot d x + coneDot d b) := by
    unfold coneDot
    fun_prop
  have hlimit := tendsto_integral_remove_exponential_damping hMeas.aemeasurable hNonneg hFourier
  have hc : Tendsto (fun t : ℝ => Real.exp (t * coneDot d b)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [ContinuousWithinAt, zero_mul, Real.exp_zero] using
      (show Continuous fun t : ℝ => Real.exp (t * coneDot d b) by fun_prop)
        |>.continuousWithinAt (s := Ioi 0) (x := 0)
  have hlimit' := hc.smul hlimit
  rw [one_smul] at hlimit'
  refine hlimit'.congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with t ht
  rw [regularizedOrthantTerm_integral d b hd P hf ht, ← integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [smul_smul, ← Real.exp_add]
    apply congrArg (fun r : ℝ => Real.exp r • _)
    ring

/-- On a ray whose slopes are strictly positive in every coroot coordinate,
only the all-positive oriented Fourier test survives. -/
theorem translatedOrthant_polynomialTest_tendsto (d b v : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (hv : ∀ i, 0 < v i) (ν : Measure (ι → ℝ)) (f : (ι → ℝ) → ℂ)
    (P : MvPolynomial ι ℂ) (hF : Integrable (orthantPolynomialTest ν f P)) :
    Tendsto (fun n : ℕ => ∫ x in translatedOrientedOrthant d (b + (n : ℝ) • v),
      orthantPolynomialTest ν f P x) atTop
      (𝓝 (if ∀ i, 0 < d i then ∫ x, orthantPolynomialTest ν f P x else 0)) := by
  have hEq (n : ℕ) : {x : ι → ℝ | ∀ i, 0 < (x i + b i + n * v i) * d i} =
      translatedOrientedOrthant d (b + (n : ℝ) • v) := by
    ext x
    simp [mem_translatedOrientedOrthant hd, add_assoc]
  have h := translatedConeIntegralLimit volume (fun i x => x i + b i) v d
    (fun i => (measurable_pi_apply i).add_const _) hv hF
  by_cases hpos : ∀ i, 0 < d i
  · simpa only [hEq, ite_eq_left hpos] using h
  · simpa only [hEq, ite_eq_right hpos] using h

end Langlands.Global
