import Langlands.Automorphic.CuspidalAdmissible.CentralEigen
import Langlands.Global.RankinSelberg.RealLocalAdjacentUnfolding
import Langlands.Global.RankinSelberg.RealEqualConvergence
import Langlands.Representation.Archimedean.RealStandardCentralExponent
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Order.Compact

/-! # Spectral multiplication for ordinary real equal-rank integrals -/

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace Langlands.Global.RankinSelbergGlobal.RealEqualSpectralMultiplication

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open Langlands.QuotientIntegration (descend rightTranslate)
open ArchimedeanLocal RealEqualConvergence
open RealLocalWhittaker (model_le_regularFunctions)
open RealJacquet (realDetPower_mul)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Q" => LeftUnipotentQuotient r ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Row" => Fin (r + 1) → ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

/-- The derivative of the row Schwartz test along positive scalar dilations. -/
def radialDerivative (Φ : 𝓢(Row, ℂ)) : 𝓢(Row, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ ℂ).flip
    (ContinuousLinearMap.id ℝ Row).hasTemperateGrowth (SchwartzMap.fderivCLM ℝ Row ℂ Φ)

@[simp] theorem radialDerivative_apply (Φ : 𝓢(Row, ℂ)) (v : Row) :
    radialDerivative Φ v = fderiv ℝ Φ v v := rfl

private theorem hasDerivAt_dilatedRow (Φ : 𝓢(Row, ℂ)) (v : Row) (x : ℝ) :
    HasDerivAt (fun u : ℝ => Φ (Real.exp u • v))
      (radialDerivative Φ (Real.exp x • v)) x := by
  simpa only [Function.comp_def, radialDerivative_apply] using
    (Φ.hasFDerivAt (Real.exp x • v)).comp_hasDerivAt x ((Real.hasDerivAt_exp x).smul_const v)

private def scalar (x : ℝ) : G :=
  GeneralLinear.scalar (Units.mk0 (Real.exp x) (Real.exp_pos x).ne')

private theorem matrixExpUnit_identity (x : ℝ) :
    matrixExpUnit (r + 1) (x • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) = scalar (r := r) x := by
  rw [show x • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) = Matrix.diagonal (fun _ => x) by
    ext i j
    by_cases h : i = j <;> simp [h], RealPrincipalSeriesDuality.matrixExpUnit_diagonal]
  rfl

private theorem coefficient_mul_scalar {ds : List RealBlock} {a : ℝˣ}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B)
    (f : Automorphic.realStandardKFinite (r + 1) ds) (g : G) (x : ℝ) :
    B f (g * scalar x) = Complex.exp (realStandardCentralExponent (r + 1) ds * x) * B f g := by
  let lam := realStandardCentralExponent (r + 1) ds
  let X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := 1
  let u (t : ℝ) := g * matrixExpUnit (r + 1) (t • X)
  have hR (k : G) : rightDerivative (matrixModel ℝ (r + 1)) X (B f) k = lam * B f k := by
    have hF := hB.2.2.2.2 X f (realStandardLie (r + 1) ds (1 ⊗ₜ[ℝ] X) f)
      (realStandardLie_one_tmul_apply_coe (r + 1) ds X f)
    rw [show X = 1 from rfl, realStandardLie_identity, map_smul] at hF
    exact (congrFun hF k).symm
  have hd (t : ℝ) : HasDerivAt (fun z => B f (u z)) (lam * B f (u t)) t := by
    have h := (differentiableAt_unitsExtension (hB.2.1 f) (Units.isUnit (u t))).hasFDerivAt
    have hval (z : ℝ) : (u z).val = g.val * NormedSpace.exp (z • X) := rfl
    have hu : HasDerivAt (fun z => (u z).val) ((u t).val * X) t := by
      simp_rw [hval]
      simpa only [Matrix.mul_assoc] using (hasDerivAt_exp_smul_const X t).const_mul g.val
    have hc := h.comp_hasDerivAt t hu
    rw [← rightDerivative_eq_fderiv (hB.2.1 f), hR] at hc
    simpa only [Function.comp_def, unitsExtension_val] using hc
  have heq := Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt hd x
  change B f (g * matrixExpUnit (r + 1) (x • X)) =
    Complex.exp (lam * x) * B f (g * matrixExpUnit (r + 1) ((0 : ℝ) • X)) at heq
  rw [zero_smul, matrixExpUnit_zero, mul_one] at heq
  simpa only [X, lam, matrixExpUnit_identity] using heq

private theorem model_mul_scalar {ds : List RealBlock} {a : ℝˣ}
    (W : realWhittakerModel r ds a) (g : G) (x : ℝ) :
    W.val (g * scalar x) = Complex.exp (realStandardCentralExponent (r + 1) ds * x) * W.val g := by
  let L : (G → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.proj (g * scalar x) - Complex.exp (realStandardCentralExponent (r + 1) ds * x) • LinearMap.proj g
  have hle : realWhittakerModel r ds a ≤ LinearMap.ker L := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    exact sub_eq_zero.mpr (coefficient_mul_scalar hB f g x)
  exact sub_eq_zero.mp (hle W.property)

private theorem lastRow_mul_scalar (x : ℝ) (g : G) :
    lastRow (g * scalar x) = Real.exp x • lastRow g := by
  funext j
  change (g.val * Matrix.diagonal (fun _ : Fin (r + 1) => Real.exp x)) (Fin.last r) j =
    Real.exp x * g.val (Fin.last r) j
  rw [Matrix.mul_diagonal, mul_comm]

private theorem detPower_scalar (x : ℝ) (s : ℂ) :
    P (scalar (r := r) x) s = Complex.exp (((r : ℂ) + 1) * s * x) := by
  change Complex.exp (s * (Real.log |(Matrix.diagonal (fun _ : Fin (r + 1) => Real.exp x)).det| : ℝ)) = _
  simp only [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    abs_pow, abs_of_nonneg (Real.exp_nonneg _), Real.log_pow, Real.log_exp, Complex.ofReal_mul,
    Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
  congr 1
  ring

variable {d e : List RealBlock} {a : ℝˣ}

private theorem pair_invariant (W : realWhittakerModel r d a) (V : realWhittakerModel r e (-a))
    (u : N) (g : G) : W.val (u.val * g) * V.val (u.val * g) = W.val g * V.val g := by
  rw [(model_le_regularFunctions d a W.property).1 u.val u.property g,
    (model_le_regularFunctions e (-a) V.property).1 u.val u.property g]
  calc
    _ = (realWhittakerCharacter a u.val * realWhittakerCharacter (-a) u.val) * (W.val g * V.val g) := by ring
    _ = _ := by rw [realWhittakerCharacter_mul_neg, one_mul]

/-- The sum of the central exponents of the two standard modules. -/
def pairCentralExponent (r : ℕ) (d e : List RealBlock) : ℂ :=
  realStandardCentralExponent (r + 1) d + realStandardCentralExponent (r + 1) e

private theorem integral_dilatedRow (D : RealQuotientMeasureData r)
    (W : realWhittakerModel r d a) (V : realWhittakerModel r e (-a))
    (Φ : 𝓢(Row, ℂ)) (x : ℝ) (s : ℂ) :
    realEqualIntegral D W.val V.val (fun y => Φ (Real.exp x • y)) s =
      Complex.exp (-(((r : ℂ) + 1) * s + pairCentralExponent r d e) * x) *
        realEqualIntegral D W.val V.val Φ s := by
  let E := rightTranslate N (scalar x)
  let m := Complex.exp (-(((r : ℂ) + 1) * s + pairCentralExponent r d e) * x)
  have hm : MeasurePreserving E D.measure D.measure := by
    let := D.unipotentHaar_rightInvariant
    exact D.compatible.right_invariant _
  have hK : realEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s =
      fun q => m * realEqualIntegrand W.val V.val Φ s (E q) := by
    funext q
    change RealPlaceReflection.kernel (fun g => W.val g * V.val g)
        (fun y => Φ (Real.exp x • y)) s q.out =
      m * RealPlaceReflection.kernel (fun g => W.val g * V.val g) (Φ : Row → ℂ) s (E q).out
    rw [RealPlaceReflection.kernel_out_rightTranslate _ (pair_invariant W V)]
    simp only [RealPlaceReflection.kernel, model_mul_scalar, lastRow_mul_scalar, realDetPower_mul, detPower_scalar]
    have h : m * Complex.exp (realStandardCentralExponent (r + 1) d * x) *
        Complex.exp (realStandardCentralExponent (r + 1) e * x) *
        Complex.exp (((r : ℂ) + 1) * s * x) = 1 := by
      rw [show m = Complex.exp (-(((r : ℂ) + 1) * s + pairCentralExponent r d e) * x) by rfl]
      simp only [← Complex.exp_add, pairCentralExponent, ← Complex.exp_zero]
      apply congrArg Complex.exp
      ring
    calc
      _ = (m * Complex.exp (realStandardCentralExponent (r + 1) d * x) *
          Complex.exp (realStandardCentralExponent (r + 1) e * x) *
          Complex.exp (((r : ℂ) + 1) * s * x)) *
            (W.val q.out * V.val q.out * Φ (Real.exp x • lastRow q.out) * P q.out s) := by rw [h, one_mul]
      _ = _ := by ring
  change (∫ q, realEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s q ∂D.measure) = _
  rw [hK, integral_const_mul, hm.integral_comp E.measurableEmbedding]
  rfl

private theorem integrand_continuous (W : realWhittakerModel r d a) (V : realWhittakerModel r e (-a))
    {Φ : Row → ℂ} (hΦ : Continuous Φ) (s : ℂ) :
    Continuous (realEqualIntegrand W.val V.val Φ s) := by
  let f := RealPlaceReflection.kernel (fun g => W.val g * V.val g) Φ s
  have hf := RealPlaceReflection.kernel_unipotent_mul (fun g => W.val g * V.val g)
    (pair_invariant W V) Φ s
  rw [show (realEqualIntegrand W.val V.val Φ s) = descend N f hf from
    funext fun q => out_eq_descend f hf q]
  refine continuous_descend hf ?_
  exact (continuous_kernel (model_le_regularFunctions d a W.property).2.1.continuous
    (model_le_regularFunctions e (-a) V.property).2.1.continuous hΦ).mul
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_logDet)))

private theorem dilated_integrand_measurable (D : RealQuotientMeasureData r)
    (W : realWhittakerModel r d a) (V : realWhittakerModel r e (-a))
    (Φ : 𝓢(Row, ℂ)) (s : ℂ) (x : ℝ) :
    AEStronglyMeasurable (realEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s) D.measure := by
  have hscale : Continuous (fun y : Row => Real.exp x • y) := by fun_prop
  exact (integrand_continuous W V (Φ.continuous.comp hscale) s).aestronglyMeasurable

private def dilationNorm (Φ : 𝓢(Row, ℂ)) (v : Row) : ℝ :=
  sSup ((fun x : ℝ => ‖Φ (Real.exp x • v)‖) '' Icc (-1 : ℝ) 1)

private theorem dilationNorm_attained (Φ : 𝓢(Row, ℂ)) (v : Row) :
    ∃ x ∈ Icc (-1 : ℝ) 1, dilationNorm Φ v = ‖Φ (Real.exp x • v)‖ ∧
      ∀ y ∈ Icc (-1 : ℝ) 1, ‖Φ (Real.exp y • v)‖ ≤ ‖Φ (Real.exp x • v)‖ :=
  isCompact_Icc.exists_sSup_image_eq_and_ge (nonempty_Icc.mpr (by norm_num))
    (Φ.continuous.comp (Real.continuous_exp.smul continuous_const)).norm.continuousOn

private theorem dilationNorm_continuous (Φ : 𝓢(Row, ℂ)) : Continuous (dilationNorm Φ) := by
  exact isCompact_Icc.continuous_sSup (by fun_prop :
    Continuous (fun p : Row × ℝ => ‖Φ (Real.exp p.2 • p.1)‖))

private theorem dilationNorm_rapid (Φ : 𝓢(Row, ℂ)) :
    HasRapidDecay (fun v => (dilationNorm Φ v : ℂ)) := by
  intro k
  obtain ⟨C, hC⟩ := hasRapidDecay_schwartz Φ k
  refine ⟨(Real.exp 1) ^ k * C, fun v => ?_⟩
  change ‖v‖ ^ k * ‖(dilationNorm Φ v : ℂ)‖ ≤ _
  obtain ⟨x, hx, hmax, _⟩ := dilationNorm_attained Φ v
  rw [hmax, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  have hv : v = Real.exp (-x) • (Real.exp x • v) := by
    rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  have hnorm := congrArg norm hv
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)] at hnorm
  calc
    ‖v‖ ^ k * ‖Φ (Real.exp x • v)‖ =
        Real.exp (-x) ^ k * (‖Real.exp x • v‖ ^ k * ‖Φ (Real.exp x • v)‖) := by
      rw [← mul_assoc, ← mul_pow, ← hnorm]
    _ ≤ Real.exp 1 ^ k * C :=
      mul_le_mul (pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr (by linarith [hx.1])) _)
        (hC _) (by positivity) (by positivity)

private theorem dilation_domination (D : RealQuotientMeasureData r)
    (W : realWhittakerModel r d a) (V : realWhittakerModel r e (-a))
    (hW : HasGauge W.val) (hV : HasGauge V.val) (Φ : 𝓢(Row, ℂ)) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re → ∃ M : Q → ℝ, Integrable M D.measure ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q : Q,
        ‖realEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s q‖ ≤ M q := by
  let F (v : Row) : ℂ := dilationNorm Φ v
  obtain ⟨b, hb, _⟩ := exists_convergence D
    (model_le_regularFunctions d a W.property).2.1.continuous
    (model_le_regularFunctions e (-a) V.property).2.1.continuous
    (Complex.continuous_ofReal.comp (dilationNorm_continuous Φ))
    (fun u hu g => pair_invariant W V ⟨u, hu⟩ g) hW hV (dilationNorm_rapid Φ)
  refine ⟨b, fun s hs => ⟨fun q => ‖realEqualIntegrand W.val V.val F s q‖,
    (hb s hs).norm, fun x hx q => ?_⟩⟩
  obtain ⟨t, _, hmax, hle⟩ := dilationNorm_attained Φ (lastRow q.out)
  simp only [realEqualIntegrand, ArchimedeanLocal.equalIntegrand, norm_mul, F, hmax,
    Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  gcongr
  exact hle x hx

/-- On a common right half-plane, the radial derivative of a Schwartz row
realizes the affine spectral multiplier given by the central exponents. -/
def RealEqualSpectralMultiplicationStatement : Prop :=
  ∀ (r : ℕ) (d e : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData r)
    (W : realWhittakerModel r d a) (V : realWhittakerModel r e (-a)),
    HasGauge W.val → HasGauge V.val → ∀ (Φ : 𝓢((Fin (r + 1) → ℝ), ℂ)),
      ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        realEqualIntegral D W.val V.val (radialDerivative Φ) s =
          (-(((r : ℂ) + 1) * s + pairCentralExponent r d e)) * realEqualIntegral D W.val V.val Φ s

set_option maxHeartbeats 1300000 in
theorem realEqualSpectralMultiplication : RealEqualSpectralMultiplicationStatement := by
  intro r d e a D W V hW hV Φ
  let U := radialDerivative Φ
  obtain ⟨b, hb⟩ := dilation_domination D W V hW hV Φ
  obtain ⟨b', hb'⟩ := dilation_domination D W V hW hV U
  refine ⟨max b b', fun s hs => ?_⟩
  obtain ⟨M, hM, hMb⟩ := hb s ((le_max_left _ _).trans_lt hs)
  obtain ⟨M', hM', hMb'⟩ := hb' s ((le_max_right _ _).trans_lt hs)
  let F (x : ℝ) := realEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s
  let F' (x : ℝ) := realEqualIntegrand W.val V.val (fun y => U (Real.exp x • y)) s
  have hMeas := dilated_integrand_measurable D W V Φ s
  have hMeas' := dilated_integrand_measurable D W V U s
  have hnb : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hI : Integrable (F 0) D.measure := hM.mono' (hMeas 0) (ae_of_all _ (hMb 0 h0))
  have hDeriv (x : ℝ) (q : LeftUnipotentQuotient r ℝ) : HasDerivAt (fun v => F v q) (F' x q) x := by
    simpa only [F, F', U, realEqualIntegrand, ArchimedeanLocal.equalIntegrand] using
      ((hasDerivAt_dilatedRow Φ (lastRow q.out) x).const_mul (W.val q.out * V.val q.out)).mul_const (P q.out s)
  obtain ⟨_, hIntDeriv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := M') hnb (Eventually.of_forall hMeas) hI (hMeas' 0)
    (ae_of_all _ fun q x hx => hMb' x hx q) hM' (ae_of_all _ fun q x _ => hDeriv x q)
  let c := -(((r : ℂ) + 1) * s + pairCentralExponent r d e)
  have heq : (fun x : ℝ => ∫ q, F x q ∂D.measure) =
      fun x : ℝ => Complex.exp (c * x) * realEqualIntegral D W.val V.val Φ s :=
    funext fun x => integral_dilatedRow D W V Φ x s
  have hOther : HasDerivAt (fun x : ℝ => Complex.exp (c * x) * realEqualIntegral D W.val V.val Φ s)
      (c * realEqualIntegral D W.val V.val Φ s) 0 := by
    simpa only [id_eq, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_one,
      one_mul, mul_one] using
      ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul c).cexp).mul_const (realEqualIntegral D W.val V.val Φ s)
  rw [heq] at hIntDeriv
  simpa only [F', U, Real.exp_zero, one_smul, c, realEqualIntegral, realEqualIntegrand,
    ArchimedeanLocal.equalIntegral] using hIntDeriv.unique hOther

end Langlands.Global.RankinSelbergGlobal.RealEqualSpectralMultiplication
