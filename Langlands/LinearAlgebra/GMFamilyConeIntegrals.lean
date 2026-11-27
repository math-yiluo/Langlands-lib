import Langlands.LinearAlgebra.GMFamilyExponentialBound
import Langlands.Analysis.ConeFourierBoundary

/-! # Integrals of `c_M` of an exponential family against integrable tests

The Library's `θ_S(Λ)` is `gram(Δ_S)⁻¹ ∏_{v ∈ Δ_S} iΛ(v)`, evaluated at the spectral parameter
`iΛ`. Replacing the real functional `Λ` by `Λ + iτμ` gives the spectral parameter `iΛ − τμ`,
whose factors are `iΛ(v) − τμ(v) = τ(−μ(v)) + iΛ(v)`. Hence, for every real `τ`,
`θ_S(Λ + iτμ)⁻¹ = gram(Δ_S) · orthantReciprocal (−μ(v))_v τ (Λ(v))_v`
(`thetaShift_I_mul_inv`). If moreover `τ > 0` and `μ(v) ≠ 0` for every `v ∈ Δ_S`, then by
`orthant_laplace` this equals the absolutely convergent damped integral
`gram(Δ_S) · orthantSign(−μ) · ∫ e^{−τ ∑_v (−μ(v)) X_v} e^{−i ∑_v X_v Λ(v)} dX` over the orthant
`{−μ(v) X_v > 0}`.

The main result `integral_cM_exp_mul` integrates against a test and lets `τ → 0⁺`. Its
hypotheses: the points `y` give a `(G, M)`-family of exponentials, `μ(v) ≠ 0` on the simple roots
of every chamber, `L` is a measurable map from an s-finite measure space to `StrongDual ℝ a` with
`L w (v) ≠ 0` on all these simple roots for almost every `w`, the test `u` is integrable, and for
every chamber `S` the Fourier integral `X ↦ ∫ e^{−i ∑_v X_v L(w)(v)} e^{iL(w)(y_S)} u(w) dν` of
the phased test is integrable on the orthant `{−μ(v) X_v > 0}`. Its conclusion: the integral of
`c_M(L w) u(w)` is the sum over chambers of Gram factors, orientation signs and the undamped
orthant integrals of these Fourier integrals. Off the walls `θ_S(Λ + iτμ)⁻¹` converges pointwise to
the ordinary reciprocal `θ_S(Λ)⁻¹`; the undamped orthant integral is a boundary value only in the
sense of the limit of the integrals against the test (in rank one, `(τ + ix)⁻¹` paired with
`e^{−x²}` has real part tending to `π`, although `(ix)⁻¹` is purely imaginary). The passage to the
limit uses the uniform bound of `Langlands.GMFamily.norm_expShift_le`. -/

noncomputable section

open scoped RealInnerProductSpace Topology ContDiff
open Filter Finset Classical Complex MeasureTheory
open Langlands.Analysis

namespace Langlands.GMFamily

section Orthant

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem orientedOrthant_eq (d : ι → ℝ) :
    orientedOrthant d = Set.univ.pi fun i => if 0 < d i then Set.Ioi 0 else Set.Iio 0 := rfl

theorem orthantReciprocal_eq (d : ι → ℝ) (t : ℝ) (y : ι → ℝ) :
    orthantReciprocal d t y = ∏ i, (((t * d i : ℝ) : ℂ) + I * (y i : ℂ))⁻¹ := rfl

theorem orthantSign_mul_self (d : ι → ℝ) : orthantSign d * orthantSign d = 1 := by
  rw [orthantSign, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => by split_ifs <;> norm_num

theorem exp_orthant_exponent (d : ι → ℝ) (t : ℝ) (x y : ι → ℝ) :
    Complex.exp (∑ i, -(((t * d i : ℝ) : ℂ) + I * (y i : ℂ)) * (x i : ℂ)) =
      Real.exp (-(t * ∑ i, d i * x i)) •
        Complex.exp (I * ((-(∑ i, x i * y i) : ℝ) : ℂ)) := by
  rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have h1 : ∀ i, -(((t * d i : ℝ) : ℂ) + I * (y i : ℂ)) * (x i : ℂ) =
      ((-(t * (d i * x i)) : ℝ) : ℂ) + I * ((-(x i * y i) : ℝ) : ℂ) := fun i => by
    push_cast; ring
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_sum, ← Complex.ofReal_sum, Finset.sum_neg_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]

/-- **Fubini for orthant reciprocals.** Let `d_i ≠ 0` for every `i` and `t > 0`. For a measurable
family of coordinates `y` on an s-finite measure space and an integrable test `g`, the integral of
`g` against the product of `(t d_i + i y_i)⁻¹`, multiplied by the orientation sign `orthantSign d`,
is the exponentially damped orthant integral of the Fourier integral of `g`. -/
theorem orthantReciprocal_integral' {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]
    (y : Ω → ι → ℝ) (hy : Measurable y) (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) {g : Ω → ℂ}
    (hg : Integrable g ν) {t : ℝ} (ht : 0 < t) :
    orthantSign d * (∫ w, orthantReciprocal d t (y w) * g w ∂ν) =
      ∫ x in orientedOrthant d, Real.exp (-(t * ∑ i, d i * x i)) •
        ∫ w, Complex.exp (I * ((-(∑ i, x i * y w i) : ℝ) : ℂ)) * g w ∂ν := by
  let μ : Measure (ι → ℝ) := volume.restrict (orientedOrthant d)
  let r (x : ι → ℝ) : ℝ := Real.exp (-(t * ∑ i, d i * x i))
  have laplace (z : ι → ℝ) :
      IntegrableOn (fun x : ι → ℝ =>
        Complex.exp (∑ i, -(((t * d i : ℝ) : ℂ) + I * (z i : ℂ)) * (x i : ℂ)))
        (orientedOrthant d) ∧
      (∫ x in orientedOrthant d,
        Complex.exp (∑ i, -(((t * d i : ℝ) : ℂ) + I * (z i : ℂ)) * (x i : ℂ))) =
        orthantSign d * orthantReciprocal d t z :=
    orthant_laplace d t z hd ht
  have hr : Integrable r μ := by
    have h := (laplace 0).1.norm
    refine h.congr (ae_of_all _ fun x => ?_)
    dsimp only
    rw [exp_orthant_exponent, norm_smul, Complex.norm_exp_I_mul_ofReal, mul_one,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  let k (x : ι → ℝ) (w : Ω) : ℂ := Complex.exp (I * ((-(∑ i, x i * y w i) : ℝ) : ℂ))
  have hk : Measurable (fun p : (ι → ℝ) × Ω => k p.1 p.2) := by
    unfold k
    refine Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp ?_))
    refine Measurable.neg (Finset.measurable_sum _ fun i _ => ?_)
    exact (measurable_pi_apply i |>.comp measurable_fst).mul
      ((measurable_pi_apply i).comp (hy.comp measurable_snd))
  have hnk (x : ι → ℝ) (w : Ω) : ‖k x w‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hrCont : Continuous r := by unfold r; fun_prop
  let G (x : ι → ℝ) (w : Ω) : ℂ := r x • (k x w * g w)
  have hG : Integrable (Function.uncurry G) (μ.prod ν) := by
    refine (hr.smul_prod hg).mono ?_ (ae_of_all _ fun p => ?_)
    · exact hrCont.aestronglyMeasurable.comp_fst.smul
        (hk.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd)
    · change ‖r p.1 • (k p.1 p.2 * g p.2)‖ ≤ ‖r p.1 • g p.2‖
      simp only [norm_smul, norm_mul, hnk, one_mul, le_refl]
  calc
    _ = ∫ w, (∫ x, G x w ∂μ) ∂ν := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all ν fun w => by
        have hL := (laplace (y w)).2
        simp only [exp_orthant_exponent] at hL
        change orthantSign d * (orthantReciprocal d t (y w) * g w) =
          ∫ x, r x • (k x w * g w) ∂μ
        simp_rw [Complex.real_smul, ← mul_assoc]
        rw [integral_mul_const]
        exact congrArg (fun z : ℂ => z * g w) (by rw [← hL]; rfl)
    _ = ∫ x, (∫ w, G x w ∂ν) ∂μ := (integral_integral_swap hG).symm
    _ = _ := by
      simp_rw [G, integral_smul]
      rfl

/-- **Boundary value of orthant reciprocals.** Let `d_i ≠ 0` for every `i`, let `y` be a measurable
family of coordinates on an s-finite measure space, let the test `g` be integrable, and let the
Fourier integral `x ↦ ∫ e^{−i ∑ x_i y_i(w)} g(w) dν` be integrable on the orthant `{d_i x_i > 0}`.
Then the integrals of the test against `∏_i (t d_i + i y_i)⁻¹` converge as `t → 0⁺` to
`orthantSign d` times the undamped orthant integral of the Fourier integral. -/
theorem tendsto_orthantReciprocal_integral {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [SFinite ν] (y : Ω → ι → ℝ) (hy : Measurable y) (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    {g : Ω → ℂ} (hg : Integrable g ν)
    (hF : IntegrableOn (fun x : ι → ℝ =>
      ∫ w, Complex.exp (I * ((-(∑ i, x i * y w i) : ℝ) : ℂ)) * g w ∂ν) (orientedOrthant d)) :
    Tendsto (fun t : ℝ => ∫ w, orthantReciprocal d t (y w) * g w ∂ν) (𝓝[>] 0)
      (𝓝 (orthantSign d * ∫ x in orientedOrthant d,
        ∫ w, Complex.exp (I * ((-(∑ i, x i * y w i) : ℝ) : ℂ)) * g w ∂ν)) := by
  have hNonneg : ∀ᵐ x ∂(volume.restrict (orientedOrthant d)), 0 ≤ ∑ i, d i * x i := by
    refine (ae_restrict_mem (measurableSet_orientedOrthant d)).mono fun x hx => ?_
    rw [orientedOrthant_eq] at hx
    refine Finset.sum_nonneg fun i _ => ?_
    have hi := hx i (Set.mem_univ _)
    by_cases hp : 0 < d i
    · simp only [hp, ↓reduceIte, Set.mem_Ioi] at hi
      exact mul_nonneg hp.le hi.le
    · simp only [hp, ↓reduceIte, Set.mem_Iio] at hi
      exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hp) hi.le
  have hMeas : Measurable (fun x : ι → ℝ => ∑ i, d i * x i) := by fun_prop
  have hlim := (tendsto_integral_remove_exponential_damping hMeas.aemeasurable hNonneg hF).const_mul
    (orthantSign d)
  refine hlim.congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with t ht
  rw [← orthantReciprocal_integral' y hy d hd hg ht, ← mul_assoc, orthantSign_mul_self, one_mul]

end Orthant

section Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {R : Finset E} {a : Submodule ℝ E}

omit [FiniteDimensional ℝ E] in
theorem norm_orthantReciprocal_le {ι : Type*} [Fintype ι] {d : ι → ℝ} (hd : ∀ i, d i ≠ 0)
    {t : ℝ} (ht : 0 < t) (y : ι → ℝ) : ‖orthantReciprocal d t y‖ ≤ ∏ i, |t * d i|⁻¹ := by
  rw [orthantReciprocal_eq, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_inv]
  have h0 : t * d i ≠ 0 := mul_ne_zero ht.ne' (hd i)
  refine inv_anti₀ (abs_pos.mpr h0) ?_
  have := Complex.abs_re_le_norm (((t * d i : ℝ) : ℂ) + I * (y i : ℂ))
  simpa using this

theorem thetaShift_I_mul_inv (S : Finset E) (Λ μ : StrongDual ℝ a) (τ : ℝ) :
    (thetaShift a S Λ μ (τ * I))⁻¹ =
      (gramVolume (fun v : simpleRoots a S => ((v : a) : E)) : ℂ) *
        orthantReciprocal (fun v : simpleRoots a S => -μ (v : a)) τ (fun v => Λ (v : a)) := by
  rw [thetaShift, orthantReciprocal_eq, mul_inv, inv_inv, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem continuousAt_expShift_zero (hR : IsRootSet R) (ha : IsLeviSpace R a) (y : Finset E → a)
    {Λ μ : StrongDual ℝ a} (hΛ : ∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, Λ v ≠ 0) :
    ContinuousAt (expShift R a y Λ μ) 0 := by
  unfold expShift
  refine tendsto_finsetSum _ fun S hS => ?_
  refine ContinuousAt.mul ?_ (ContinuousAt.inv₀ (differentiable_thetaShift S Λ μ).continuous.continuousAt
    (thetaShift_ne_zero hR ha hS fun v hv => by simpa using hΛ S hS v hv))
  exact (continuous_const.mul (continuous_const.add (continuous_id.mul continuous_const))).cexp.continuousAt

theorem expShift_zero (y : Finset E → a) (Λ μ : StrongDual ℝ a) :
    expShift R a y Λ μ 0 = cM R a (fun S Λ' => exp (I * (Λ' (y S) : ℂ))) Λ := by
  have h := expShift_ofReal (R := R) y Λ μ 0
  simpa using h

theorem measurable_expShift (y : Finset E → a) (μ : StrongDual ℝ a) (s : ℂ) :
    Measurable (fun Λ : StrongDual ℝ a => expShift R a y Λ μ s) := by
  unfold expShift thetaShift
  refine Finset.measurable_sum _ fun S _ => ?_
  refine Measurable.mul ?_ (Measurable.inv (measurable_const.mul ?_))
  · refine Complex.measurable_exp.comp (measurable_const.mul (Measurable.add ?_ measurable_const))
    exact Complex.measurable_ofReal.comp (ContinuousLinearMap.apply ℝ ℝ (y S)).continuous.measurable
  · refine Finset.measurable_prod _ fun v _ => measurable_const.mul (Measurable.add ?_ measurable_const)
    exact Complex.measurable_ofReal.comp (ContinuousLinearMap.apply ℝ ℝ (v : a)).continuous.measurable

/-- **Integral of `c_M` of an exponential family against an integrable test.** Let the points `y`
give a `(G, M)`-family of exponentials `e^{iΛ(y_S)}`, let `μ` be nonvanishing on all simple roots,
let `L` be a measurable map from an s-finite measure space to `StrongDual ℝ a` with `L w` off the
walls for almost every `w`, let `u` be integrable, and for each
chamber `S` let the Fourier integral of the test `w ↦ e^{iL(w)(y_S)} u(w)` be integrable on the
orthant `{−μ(v) X_v > 0}`. Then the integral of `c_M(L w) u(w)` is the sum over chambers `S` of
the orthant integral of that Fourier integral, multiplied by the Gram volume of the simple roots
`Δ_S` and by `orthantSign`, the product of the signs of `−μ` on `Δ_S`. -/
theorem integral_cM_exp_mul {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]
    (hR : IsRootSet R) (ha : IsLeviSpace R a) (y : Finset E → a)
    (hy : IsFamily R a (fun S Λ => exp (I * (Λ (y S) : ℂ)))) (μ : StrongDual ℝ a)
    (hμ : ∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, μ v ≠ 0)
    (L : Ω → StrongDual ℝ a) (hL : Measurable L) {u : Ω → ℂ} (hu : Integrable u ν)
    (hwall : ∀ᵐ w ∂ν, ∀ S ∈ parabolics R a, ∀ v ∈ simpleRoots a S, L w v ≠ 0)
    (hF : ∀ S ∈ parabolics R a, IntegrableOn (fun X : simpleRoots a S → ℝ =>
        ∫ w, exp (I * ((-(∑ v, X v * L w (v : a)) : ℝ) : ℂ)) *
          (exp (I * (L w (y S) : ℂ)) * u w) ∂ν)
        (orientedOrthant (fun v : simpleRoots a S => -μ (v : a)))) :
    ∫ w, cM R a (fun S Λ => exp (I * (Λ (y S) : ℂ))) (L w) * u w ∂ν =
      ∑ S ∈ parabolics R a, (gramVolume (fun v : simpleRoots a S => ((v : a) : E)) : ℂ) *
        (orthantSign (fun v : simpleRoots a S => -μ (v : a)) *
          ∫ X in orientedOrthant (fun v : simpleRoots a S => -μ (v : a)),
            ∫ w, exp (I * ((-(∑ v, X v * L w (v : a)) : ℝ) : ℂ)) *
              (exp (I * (L w (y S) : ℂ)) * u w) ∂ν) := by
  let K := expShiftBound R a y μ
  let f : ℝ → ℂ := fun τ => ∫ w, expShift R a y (L w) μ (τ * I) * u w ∂ν
  -- the test multiplied by the phase of each chamber
  have hphase (S : Finset E) : Integrable (fun w => exp (I * (L w (y S) : ℂ)) * u w) ν := by
    refine hu.bdd_mul (c := 1) ?_ (ae_of_all _ fun w => ?_)
    · exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        ((ContinuousLinearMap.apply ℝ ℝ (y S)).continuous.measurable.comp hL)))).aestronglyMeasurable
    · rw [Complex.norm_exp_I_mul_ofReal]
  have hcoord (S : Finset E) : Measurable (fun w (v : simpleRoots a S) => L w (v : a)) :=
    measurable_pi_iff.mpr fun v => (ContinuousLinearMap.apply ℝ ℝ (v : a)).continuous.measurable.comp hL
  have hd (S : Finset E) (hS : S ∈ parabolics R a) :
      ∀ v : simpleRoots a S, -μ (v : a) ≠ 0 := fun v => neg_ne_zero.mpr (hμ S hS v v.property)
  -- step A: dominated convergence as `τ → 0⁺`
  have hA : Tendsto f (𝓝[>] 0)
      (𝓝 (∫ w, cM R a (fun S Λ => exp (I * (Λ (y S) : ℂ))) (L w) * u w ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun w => K * ‖u w‖) ?_ ?_
      (hu.norm.const_mul K) ?_
    · exact Eventually.of_forall fun τ =>
        ((measurable_expShift y μ _).comp hL).aestronglyMeasurable.mul hu.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with τ hτ
      refine ae_of_all _ fun w => ?_
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine norm_expShift_le hR ha y hy μ hμ (L w) (by simp) ?_ fun S hS v hv => ?_
      · simp [abs_of_pos hτ.1, hτ.2.le]
      · intro h0
        have him := congrArg Complex.im h0
        simp at him
        rcases him with h | h
        · exact absurd h hτ.1.ne'
        · exact hμ S hS v hv h
    · filter_upwards [hwall] with w hw
      have hcont := continuousAt_expShift_zero hR ha y (μ := μ) hw
      have h0 : Tendsto (fun τ : ℝ => (τ : ℂ) * I) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun τ : ℝ => (τ : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
          (Complex.continuous_ofReal.mul continuous_const).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have := (hcont.tendsto.comp h0).mul_const (u w)
      rwa [Function.comp_def, expShift_zero] at this
  -- step B: the shifted integral as a sum of orthant reciprocal integrals
  have hB : ∀ τ : ℝ, 0 < τ → f τ = ∑ S ∈ parabolics R a,
      (Real.exp (-(τ * μ (y S))) : ℂ) * ((gramVolume (fun v : simpleRoots a S => ((v : a) : E)) : ℂ) *
        ∫ w, orthantReciprocal (fun v : simpleRoots a S => -μ (v : a)) τ (fun v => L w (v : a)) *
          (exp (I * (L w (y S) : ℂ)) * u w) ∂ν) := by
    intro τ hτ
    have hterm (S : Finset E) (w : Ω) :
        exp (I * ((L w (y S) : ℂ) + (τ * I) * (μ (y S) : ℂ))) * (thetaShift a S (L w) μ (τ * I))⁻¹ *
          u w = (Real.exp (-(τ * μ (y S))) : ℂ) *
            ((gramVolume (fun v : simpleRoots a S => ((v : a) : E)) : ℂ) *
              (orthantReciprocal (fun v : simpleRoots a S => -μ (v : a)) τ (fun v => L w (v : a)) *
                (exp (I * (L w (y S) : ℂ)) * u w))) := by
      rw [thetaShift_I_mul_inv, Complex.ofReal_exp]
      have he : exp (I * ((L w (y S) : ℂ) + (τ * I) * (μ (y S) : ℂ))) =
          exp ((-(τ * μ (y S)) : ℝ) : ℂ) * exp (I * (L w (y S) : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [he]
      ring
    have hint (S : Finset E) (hS : S ∈ parabolics R a) : Integrable (fun w =>
        orthantReciprocal (fun v : simpleRoots a S => -μ (v : a)) τ (fun v => L w (v : a)) *
          (exp (I * (L w (y S) : ℂ)) * u w)) ν := by
      refine (hphase S).bdd_mul (c := ∏ v : simpleRoots a S, |τ * -μ (v : a)|⁻¹) ?_
        (ae_of_all _ fun w => norm_orthantReciprocal_le (hd S hS) hτ _)
      refine Measurable.aestronglyMeasurable ?_
      rw [show (fun w => orthantReciprocal (fun v : simpleRoots a S => -μ (v : a)) τ
          (fun v => L w (v : a))) = fun w => ∏ v : simpleRoots a S,
            (((τ * -μ (v : a) : ℝ) : ℂ) + I * (L w (v : a) : ℂ))⁻¹ from rfl]
      refine Finset.measurable_prod _ fun v _ => Measurable.inv (measurable_const.add
        (measurable_const.mul ?_))
      exact Complex.measurable_ofReal.comp
        ((ContinuousLinearMap.apply ℝ ℝ (v : a)).continuous.measurable.comp hL)
    simp only [f, expShift, Finset.sum_mul]
    rw [integral_finsetSum _ fun S hS => ?_]
    · refine Finset.sum_congr rfl fun S hS => ?_
      simp_rw [hterm S]
      rw [integral_const_mul, integral_const_mul]
    · simp_rw [hterm S]
      exact ((hint S hS).const_mul _).const_mul _
  -- step C: the limit of the orthant reciprocal integrals
  have hC : Tendsto f (𝓝[>] 0) (𝓝 (∑ S ∈ parabolics R a,
      (gramVolume (fun v : simpleRoots a S => ((v : a) : E)) : ℂ) *
        (orthantSign (fun v : simpleRoots a S => -μ (v : a)) *
          ∫ X in orientedOrthant (fun v : simpleRoots a S => -μ (v : a)),
            ∫ w, exp (I * ((-(∑ v, X v * L w (v : a)) : ℝ) : ℂ)) *
              (exp (I * (L w (y S) : ℂ)) * u w) ∂ν))) := by
    have hlim : Tendsto (fun τ : ℝ => ∑ S ∈ parabolics R a,
        (Real.exp (-(τ * μ (y S))) : ℂ) * ((gramVolume (fun v : simpleRoots a S => ((v : a) : E)) : ℂ) *
          ∫ w, orthantReciprocal (fun v : simpleRoots a S => -μ (v : a)) τ (fun v => L w (v : a)) *
            (exp (I * (L w (y S) : ℂ)) * u w) ∂ν)) (𝓝[>] 0) (𝓝 (∑ S ∈ parabolics R a,
        (gramVolume (fun v : simpleRoots a S => ((v : a) : E)) : ℂ) *
          (orthantSign (fun v : simpleRoots a S => -μ (v : a)) *
            ∫ X in orientedOrthant (fun v : simpleRoots a S => -μ (v : a)),
              ∫ w, exp (I * ((-(∑ v, X v * L w (v : a)) : ℝ) : ℂ)) *
                (exp (I * (L w (y S) : ℂ)) * u w) ∂ν))) := by
      refine tendsto_finsetSum _ fun S hS => ?_
      have hexp : Tendsto (fun τ : ℝ => (Real.exp (-(τ * μ (y S))) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
        have : Tendsto (fun τ : ℝ => (Real.exp (-(τ * μ (y S))) : ℂ)) (𝓝 0)
            (𝓝 (Real.exp (-(0 * μ (y S))) : ℂ)) :=
          (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
            ((continuous_id.mul continuous_const).neg))).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have hor := tendsto_orthantReciprocal_integral (fun w (v : simpleRoots a S) => L w (v : a))
        (hcoord S) (fun v : simpleRoots a S => -μ (v : a)) (hd S hS) (hphase S) (hF S hS)
      simpa using hexp.mul (hor.const_mul (gramVolume (fun v : simpleRoots a S => ((v : a) : E)) : ℂ))
    refine hlim.congr' ?_
    filter_upwards [(self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with τ hτ
    exact (hB τ hτ).symm
  exact tendsto_nhds_unique hA hC

end Exponential

end Langlands.GMFamily
