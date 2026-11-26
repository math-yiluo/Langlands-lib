import Langlands.Global.RankinSelberg.ArchimedeanRealPairIdentity
import Langlands.Global.RankinSelberg.RealLocalAdjacentUnfolding
import Langlands.Global.RankinSelberg.RealUnequalOrdinaryFamily
import Langlands.Global.RankinSelberg.RealWhittakerUniformDerivativeGrowth
import Langlands.Global.RankinSelberg.OrdinaryPolynomialGeneration
import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness
import Langlands.Global.RankinSelberg.ArchimedeanRealPairFactor
import Mathlib.MeasureTheory.Integral.Prod

/-! # Spectral multiplication for ordinary real unequal-rank integrals -/

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalSpectralMultiplication

open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.QuotientIntegration (rightTranslate rightTranslate_mk leftQuotient_isOpenQuotientMap
  leftQuotientMap_apply)
open Langlands.GeneralLinear.Iwasawa (diagonalUnits_val)
open ArchimedeanLocal RealUnequalFamily
open RealJacquet (realDetPower_mul)
open RealLocalWhittaker (contMDiff_of_mem_model rightDerivative_mem_model model_le_regularFunctions)
open RealWhittakerElliptic (realIrreducibleWhittakerModelUniformity)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

local notation "G" => fun n => Langlands.GeneralLinear (n + 1) ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "ρ" => ArchimedeanLocal.translateFunction

private def firstDirection (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else 0)

private def firstDilation (n : ℕ) (x : ℝ) : G n :=
  GeneralLinear.Iwasawa.diagonalUnits (fun i => if i = 0 then
    Units.mk0 (Real.exp x) (Real.exp_pos x).ne' else 1)

private theorem firstDilation_val_eq_exp (n : ℕ) (x : ℝ) :
    (firstDilation n x).val = NormedSpace.exp (x • firstDirection n) := by
  rw [firstDilation, diagonalUnits_val, firstDirection, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Real.exp_eq_exp_ℝ]
  by_cases hi : i = 0 <;> simp [hi]

private theorem continuous_firstDilation (n : ℕ) : Continuous (firstDilation n) := by
  apply (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) (n + 1)).isInducing.continuous_iff.mpr
  simp only [Function.comp_def, firstDilation_val_eq_exp]
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

private theorem padGL_firstDilation {r t : ℕ} (h : t < r) (x : ℝ) :
    padGL (Nat.succ_le_succ h.le) (firstDilation t x) = firstDilation r x := by
  apply Units.ext
  ext i j
  rw [UnequalAnalytic.padGL_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : (i : ℕ) < t + 1
    · rw [dite_eq_left ⟨hi, hi⟩]
      simp only [firstDilation, diagonalUnits_val, Matrix.diagonal_apply_eq]
      have hzero : (⟨i.val, hi⟩ : Fin (t + 1)) = 0 ↔ i = 0 := by
        constructor
        · intro he
          exact Fin.ext (congrArg (fun v : Fin (t + 1) => v.val) he)
        · intro he
          exact Fin.ext (congrArg (fun v : Fin (r + 1) => v.val) he)
      simp only [hzero]
    · rw [dite_eq_right (fun hh => hi hh.1)]
      have hiz : i ≠ 0 := fun hz => hi (by simp [hz])
      simp [firstDilation, diagonalUnits_val, hiz]
  · by_cases hsmall : (i : ℕ) < t + 1 ∧ (j : ℕ) < t + 1
    · rw [dite_eq_left hsmall]
      have hh : (⟨i.val, hsmall.1⟩ : Fin (t + 1)) ≠ ⟨j.val, hsmall.2⟩ := fun he =>
        hij (Fin.ext (congrArg (fun v : Fin (t + 1) => v.val) he))
      simp [firstDilation, diagonalUnits_val, Matrix.diagonal_apply_ne _ hh, Matrix.diagonal_apply_ne _ hij]
    · rw [dite_eq_right hsmall]
      simp [firstDilation, diagonalUnits_val, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]

private theorem detPower_firstDilation (n : ℕ) (x : ℝ) (s : ℂ) :
    P (firstDilation n x) s = Complex.exp (s * (x : ℂ)) := by
  have hdet : (firstDilation n x).val.det = Real.exp x := by
    rw [firstDilation, diagonalUnits_val, Matrix.det_diagonal, Finset.prod_eq_single (0 : Fin (n + 1))]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [ArchimedeanLocal.detPower, hdet, realNormalizedAbs, abs_of_pos (Real.exp_pos x), Real.log_exp]

private theorem hasDerivAt_firstDilation_translate {n : ℕ} {W : G n → ℂ}
    (hW : ContMDiff (matrixModel ℝ (n + 1)) 𝓘(ℝ, ℂ) ∞ W) (y : G n) (x : ℝ) :
    HasDerivAt (fun u : ℝ => W (y * firstDilation n u))
      (rightDerivative (matrixModel ℝ (n + 1)) (firstDirection n) W (y * firstDilation n x)) x := by
  let g := y * firstDilation n x
  have hu (u : ℝ) : (y * firstDilation n u).val = y.val * NormedSpace.exp (u • firstDirection n) := by
    rw [Units.val_mul, firstDilation_val_eq_exp]
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (firstDirection n) x).const_mul y.val
  have hγ : HasDerivAt (fun u : ℝ => (y * firstDilation n u).val)
      (g.val * firstDirection n) x := by
    simpa only [hu, g, mul_assoc] using h
  have hc := (differentiableAt_unitsExtension hW g.isUnit).hasFDerivAt.comp_hasDerivAt x hγ
  have hcomp : (unitsExtension W ∘ fun u : ℝ => (y * firstDilation n u).val) =
      fun u : ℝ => W (y * firstDilation n u) := funext fun _ => unitsExtension_val _ _
  rw [hcomp] at hc
  rw [rightDerivative_eq_fderiv hW]
  exact hc

variable {r t : ℕ} (h : t < r) {d e : List RealBlock} (a : ℝˣ)
variable (D : RealQuotientMeasureData t)

private theorem leftCharacter_translate {n : ℕ} {ds : List RealBlock} {b : ℝˣ}
    (W : realWhittakerModel n ds b) (g : G n) : HasLeftCharacter b (ρ g W.val) := by
  intro u hu y
  change W.val ((u * y) * g) = _
  rw [mul_assoc]
  exact (RealLocalWhittaker.model_le_regularFunctions ds b W.property).1 u hu (y * g)

private def dilationKernel (W : G r → ℂ) (V : G t → ℂ) (s : ℂ) (x : ℝ) : Q t → ℂ :=
  realUnequalIntegrand h (ρ (firstDilation r x) W) (ρ (firstDilation t x) V) s

private theorem dilationKernel_covariant
    (W : realWhittakerModel r d a) (V : realWhittakerModel t e (-a)) (x : ℝ) (s : ℂ) :
    dilationKernel h W.val V.val s x = fun q =>
      Complex.exp ((x : ℂ) * (-(s - ((r - t : ℕ) : ℂ) / 2))) *
        realUnequalIntegrand h W.val V.val s
          (rightTranslate (GeneralLinear.upperUnipotent (t + 1) ℝ) (firstDilation t x) q) := by
  let u := firstDilation t x
  let z := s - ((r - t : ℕ) : ℂ) / 2
  let m := Complex.exp ((x : ℂ) * (-z))
  let E := rightTranslate (GeneralLinear.upperUnipotent (t + 1) ℝ) u
  have hW : HasLeftCharacter a W.val := (model_le_regularFunctions d a W.property).1
  have hV : HasLeftCharacter (-a) V.val := (model_le_regularFunctions e (-a) V.property).1
  funext q
  change realUnequalIntegrand h (ρ (firstDilation r x) W.val) (ρ u V.val) s q =
    m * realUnequalIntegrand h W.val V.val s (E q)
  induction q using Quotient.inductionOn with
  | _ g =>
    rw [show E (Quotient.mk _ g) = Quotient.mk _ (g * u) from rightTranslate_mk _ _ _,
      integrand_mk h (leftCharacter_translate W _) (leftCharacter_translate V _), integrand_mk h hW hV]
    have hu : padGL (Nat.succ_le_succ h.le) (g * u) = padGL (Nat.succ_le_succ h.le) g * firstDilation r x := by
      rw [map_mul, show u = firstDilation t x from rfl, padGL_firstDilation h]
    have hz : m * P u z = 1 := by
      rw [show u = firstDilation t x from rfl, detPower_firstDilation]
      dsimp only [m]
      rw [← Complex.exp_add, show (x : ℂ) * (-z) + z * x = 0 by ring, Complex.exp_zero]
    change W.val (padGL _ g * firstDilation r x) * V.val (g * u) * P g z =
      m * (W.val (padGL _ (g * u)) * V.val (g * u) * P (g * u) z)
    rw [hu, realDetPower_mul]
    calc
      _ = (m * P u z) * _ := by rw [hz, one_mul]
      _ = _ := by ring

private theorem continuous_dilationKernel
    (W : realWhittakerModel r d a) (V : realWhittakerModel t e (-a)) (s : ℂ) :
    Continuous (Function.uncurry (dilationKernel h W.val V.val s)) := by
  let N := GeneralLinear.upperUnipotent (t + 1) ℝ
  let z := s - ((r - t : ℕ) : ℂ) / 2
  apply (IsOpenQuotientMap.id.prodMap (leftQuotient_isOpenQuotientMap N)).continuous_comp_iff.mp
  have hEq : Function.uncurry (dilationKernel h W.val V.val s) ∘
      Prod.map (id : ℝ → ℝ) (Langlands.QuotientIntegration.leftQuotientMap N) =
      fun p : ℝ × G t =>
        W.val (padGL (Nat.succ_le_succ h.le) p.2 * firstDilation r p.1) *
          V.val (p.2 * firstDilation t p.1) *
          Complex.exp (z * (Real.log (realNormalizedAbs p.2.val.det) : ℂ)) := by
    funext p
    change realUnequalIntegrand h (ρ (firstDilation r p.1) W.val)
      (ρ (firstDilation t p.1) V.val) s (Langlands.QuotientIntegration.leftQuotientMap N p.2) = _
    rw [leftQuotientMap_apply, integrand_mk h (leftCharacter_translate W _) (leftCharacter_translate V _)]
    rfl
  rw [hEq]
  have hW := (contMDiff_of_mem_model W.property).continuous
  have hV := (contMDiff_of_mem_model V.property).continuous
  have hPad : Continuous (fun p : ℝ × G t => padGL (Nat.succ_le_succ h.le) p.2) :=
    (UnequalAnalytic.continuous_padGL _).comp continuous_snd
  have hW' : Continuous (fun p : ℝ × G t =>
      W.val (padGL (Nat.succ_le_succ h.le) p.2 * firstDilation r p.1)) :=
    hW.comp (hPad.mul ((continuous_firstDilation r).comp continuous_fst))
  have hV' : Continuous (fun p : ℝ × G t => V.val (p.2 * firstDilation t p.1)) :=
    hV.comp (continuous_snd.mul ((continuous_firstDilation t).comp continuous_fst))
  have hd : Continuous (fun p : ℝ × G t => Real.log (realNormalizedAbs p.2.val.det)) :=
    RealEqualConvergence.continuous_logDet.comp continuous_snd
  exact (hW'.mul hV').mul (Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp hd)))

/-- The infinitesimal first diagonal dilation of the actual ordinary model. -/
def firstRightDerivative {n : ℕ} {ds : List RealBlock} {b : ℝˣ}
    (W : realWhittakerModel n ds b) : realWhittakerModel n ds b :=
  ⟨rightDerivative (matrixModel ℝ (n + 1)) (firstDirection n) W.val,
    rightDerivative_mem_model W.property (firstDirection n)⟩

private theorem hasDerivAt_dilationKernel
    (W : realWhittakerModel r d a) (V : realWhittakerModel t e (-a)) (s : ℂ) (q : Q t) (x : ℝ) :
    HasDerivAt (fun y : ℝ => dilationKernel h W.val V.val s y q)
      (dilationKernel h (firstRightDerivative W).val V.val s x q +
        dilationKernel h W.val (firstRightDerivative V).val s x q) x := by
  have hW := hasDerivAt_firstDilation_translate (contMDiff_of_mem_model W.property)
    (padGL (Nat.succ_le_succ h.le) q.out) x
  have hV := hasDerivAt_firstDilation_translate (contMDiff_of_mem_model V.property) q.out x
  have hD := (hW.mul hV).mul_const (P q.out (s - ((r - t : ℕ) : ℂ) / 2))
  simpa only [dilationKernel, realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    ArchimedeanLocal.translateFunction, firstRightDerivative, Pi.mul_apply, add_mul, add_comm] using hD

private theorem integratedDerivative_of_covariance {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SFinite μ] (c : ℂ) (E : ℝ → Y ≃ᵐ Y)
    (hE : ∀ x, MeasurePreserving (E x) μ μ)
    (F F' : ℝ → Y → ℂ) (f f' : Y → ℂ) (hf : Integrable f μ) (hf' : Integrable f' μ)
    (hF : ∀ x, F x = fun y => Complex.exp ((x : ℂ) * c) * f (E x y))
    (hF' : ∀ x, F' x = fun y => Complex.exp ((x : ℂ) * c) * f' (E x y))
    (hMeas : Measurable (Function.uncurry F')) (hCont : ∀ y, Continuous (fun x => F' x y))
    (hd : ∀ x y, HasDerivAt (fun t => F t y) (F' x y) x) :
    (∫ y, f' y ∂μ) = c * (∫ y, f y ∂μ) := by
  have hFI (x : ℝ) : Integrable (F x) μ := by
    rw [hF x]
    exact ((hE x).integrable_comp_of_integrable hf).const_mul _
  have hF'I (x : ℝ) : Integrable (F' x) μ := by
    rw [hF' x]
    exact ((hE x).integrable_comp_of_integrable hf').const_mul _
  let I := ∫ y, f y ∂μ
  let J := ∫ y, f' y ∂μ
  let m (x : ℝ) := Complex.exp ((x : ℂ) * c)
  have hm : Continuous m := Complex.continuous_exp.comp (Complex.continuous_ofReal.mul_const c)
  have hInt (x : ℝ) : (∫ y, F x y ∂μ) = m x * I := by
    rw [hF x, integral_const_mul, (hE x).integral_comp (E x).measurableEmbedding]
  have hInt' (x : ℝ) : (∫ y, F' x y ∂μ) = m x * J := by
    rw [hF' x, integral_const_mul, (hE x).integral_comp (E x).measurableEmbedding]
  have hNorm (x : ℝ) : (∫ y, ‖F' x y‖ ∂μ) = ‖m x‖ * ∫ y, ‖f' y‖ ∂μ := by
    rw [hF' x]
    simp only [norm_mul]
    rw [integral_const_mul, (hE x).integral_comp (E x).measurableEmbedding (fun y => ‖f' y‖)]
  have hEq (x : ℝ) : (∫ t in 0..x, m t * J) = m x * I - m 0 * I := by
    let ν := volume.restrict (uIoc (0 : ℝ) x)
    have hi : Integrable (Function.uncurry F') (ν.prod μ) := by
      refine (integrable_prod_iff hMeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
      · exact ae_of_all ν hF'I
      change Integrable (fun t => ∫ y, ‖F' t y‖ ∂μ) ν
      simp_rw [hNorm]
      exact intervalIntegrable_iff.mp ((hm.norm.mul_const _).intervalIntegrable 0 x)
    simp_rw [← hInt']
    rw [intervalIntegral_integral_swap hi]
    have hPoint (y : Y) : (∫ t in 0..x, F' t y) = F x y - F 0 y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t y) ((hCont y).intervalIntegrable 0 x)
    simp_rw [hPoint]
    rw [integral_sub (hFI x) (hFI 0), hInt, hInt]
  have hL : HasDerivAt (fun x => ∫ t in 0..x, m t * J) J 0 := by
    have hc := hm.mul_const J
    have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
    simpa only [m, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] using h
  have hR : HasDerivAt (fun x => m x * I - m 0 * I) (c * I) 0 := by
    simpa only [m, id_eq, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      Complex.ofReal_one, one_mul, mul_one] using
      (((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const c).cexp).mul_const I).sub_const (m 0 * I)
  rw [funext hEq] at hL
  exact hL.unique hR

private theorem unequalIntegrable {ds es : List RealBlock}
    (hD : IsIrreducibleGKModule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds))
    (hE : IsIrreducibleGKModule (realStandardRep (t + 1) es) (realStandardLie (t + 1) es))
    (W : realWhittakerModel r ds a) (V : realWhittakerModel t es (-a)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h W.val V.val s) D.measure := by
  have hW : W.val ∈ realUniformWhittakerModel r ds a :=
    realIrreducibleWhittakerModelUniformity r ds a hD ▸ W.property
  have hV : V.val ∈ realUniformWhittakerModel t es (-a) :=
    realIrreducibleWhittakerModelUniformity t es (-a) hE ▸ V.property
  obtain ⟨hWr, hWg⟩ := realUniformWhittakerRegularity r ds a W.val hW
  obtain ⟨hVr, hVg⟩ := realUniformWhittakerRegularity t es (-a) V.val hV
  obtain ⟨σ, hi, _⟩ := RealUnequalConvergence.exists_convergence_of_regular h D hWr hWg hVr hVg
  exact ⟨σ, hi⟩

private def dilationShift (t : ℕ) (x : ℝ) : Q t ≃ᵐ Q t :=
  (rightTranslate (GeneralLinear.upperUnipotent (t + 1) ℝ) (firstDilation t x)).toMeasurableEquiv

private theorem measurePreserving_dilationShift (x : ℝ) :
    MeasurePreserving (dilationShift t x) D.measure D.measure := by
  let := D.unipotentHaar_rightInvariant
  exact D.compatible.right_invariant (firstDilation t x)

private theorem continuous_parameter_of_uncurry {Y : Type*} [TopologicalSpace Y]
    {F : ℝ → Y → ℂ} (hF : Continuous (Function.uncurry F)) (y : Y) :
    Continuous (fun x => F x y) := by
  have hp : Continuous (fun x : ℝ => (x, y)) := continuous_id.prodMk continuous_const
  exact hF.comp hp

set_option backward.isDefEq.respectTransparency true in
private theorem unequalIntegral_spectralDerivative_at
    (W : realWhittakerModel r d a) (V : realWhittakerModel t e (-a)) (s : ℂ)
    (hi : Integrable (realUnequalIntegrand h W.val V.val s) D.measure)
    (hi1 : Integrable (realUnequalIntegrand h (firstRightDerivative W).val V.val s) D.measure)
    (hi2 : Integrable (realUnequalIntegrand h W.val (firstRightDerivative V).val s) D.measure) :
    realUnequalIntegral h D (firstRightDerivative W).val V.val s +
      realUnequalIntegral h D W.val (firstRightDerivative V).val s =
    (-(s - ((r - t : ℕ) : ℂ) / 2)) * realUnequalIntegral h D W.val V.val s := by
  let W' := firstRightDerivative W
  let V' := firstRightDerivative V
  let f := realUnequalIntegrand h W.val V.val s
  let f₁ := realUnequalIntegrand h W'.val V.val s
  let f₂ := realUnequalIntegrand h W.val V'.val s
  let F := dilationKernel h W.val V.val s
  let F' (x : ℝ) (q : Q t) := dilationKernel h W'.val V.val s x q + dilationKernel h W.val V'.val s x q
  let c := -(s - ((r - t : ℕ) : ℂ) / 2)
  let : SigmaFinite D.measure := ArchimedeanRealPairIdentity.sigmaFinite_measure D
  have hF' (x : ℝ) : F' x = fun q =>
      Complex.exp ((x : ℂ) * c) * (f₁ + f₂) (dilationShift t x q) := by
    funext q
    change dilationKernel h W'.val V.val s x q + dilationKernel h W.val V'.val s x q = _
    rw [dilationKernel_covariant h a W' V x s, dilationKernel_covariant h a W V' x s]
    exact (mul_add _ _ _).symm
  have hC : Continuous (Function.uncurry F') :=
    (continuous_dilationKernel h a W' V s).add (continuous_dilationKernel h a W V' s)
  have hMeas : Measurable (Function.uncurry F') := by
    let : SecondCountableTopology (G t) :=
      (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) (t + 1)).isEmbedding.secondCountableTopology
    let : SecondCountableTopology (Q t) := Topology.IsOpenQuotientMap.secondCountableTopology
      (leftQuotient_isOpenQuotientMap (GeneralLinear.upperUnipotent (t + 1) ℝ))
    exact hC.measurable
  have hCont (q : Q t) : Continuous (fun x => F' x q) :=
    continuous_parameter_of_uncurry (F := F') hC q
  have hd (x : ℝ) (q : Q t) : HasDerivAt (fun u => F u q) (F' x q) x :=
    hasDerivAt_dilationKernel h a W V s q x
  have hF (x : ℝ) : F x = fun q => Complex.exp ((x : ℂ) * c) * f (dilationShift t x q) :=
    dilationKernel_covariant h a W V x s
  have hsum : Integrable (f₁ + f₂) D.measure := Integrable.add hi1 hi2
  have he := integratedDerivative_of_covariance (Y := Q t) D.measure c (dilationShift t)
    (measurePreserving_dilationShift D) F F' f (f₁ + f₂) hi hsum hF hF' hMeas hCont hd
  change (∫ q, f₁ q ∂D.measure) + (∫ q, f₂ q ∂D.measure) = c * ∫ q, f q ∂D.measure
  rw [← integral_add (f := f₁) (g := f₂) hi1 hi2]
  exact he

/-- On a common right half-plane, the sum of the two differentiated unequal-rank tests
is the original test multiplied by the negative shifted spectral parameter. -/
theorem unequalIntegral_spectralDerivative
    (hD : IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d))
    (hE : IsIrreducibleGKModule (realStandardRep (t + 1) e) (realStandardLie (t + 1) e))
    (W : realWhittakerModel r d a) (V : realWhittakerModel t e (-a)) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      realUnequalIntegral h D (firstRightDerivative W).val V.val s +
        realUnequalIntegral h D W.val (firstRightDerivative V).val s =
      (-(s - ((r - t : ℕ) : ℂ) / 2)) * realUnequalIntegral h D W.val V.val s := by
  obtain ⟨b, hb⟩ := unequalIntegrable h a D hD hE W V
  obtain ⟨b1, hb1⟩ := unequalIntegrable h a D hD hE (firstRightDerivative W) V
  obtain ⟨b2, hb2⟩ := unequalIntegrable h a D hD hE W (firstRightDerivative V)
  refine ⟨max b (max b1 b2), fun s hs => ?_⟩
  have h12 : max b1 b2 < s.re := (le_max_right b _).trans_lt hs
  exact unequalIntegral_spectralDerivative_at h a D W V s
    (hb s ((le_max_left _ _).trans_lt hs))
    (hb1 s ((le_max_left _ _).trans_lt h12))
    (hb2 s ((le_max_right _ _).trans_lt h12))

open Polynomial

private theorem realUnequalPolynomial_smul (c : ℂ) {p : ℂ[X]}
    (hp : IsOrdinaryNormalizationPolynomial (realOrdinaryUnequalTest h d e a D)
      (realPairLFactor d e) p) :
    IsOrdinaryNormalizationPolynomial (realOrdinaryUnequalTest h d e a D)
      (realPairLFactor d e) (c • p) := by
  obtain ⟨⟨W, V⟩, N, hN⟩ := hp
  let i : realWhittakerModel r d a × realWhittakerModel t e (-a) := (c • W, V)
  have hi (s : ℂ) : realOrdinaryUnequalTest h d e a D i s =
      c * realOrdinaryUnequalTest h d e a D (W, V) s := by
    simp only [i, realOrdinaryUnequalTest, realUnequalIntegral, ArchimedeanLocal.unequalIntegral,
      ArchimedeanLocal.unequalIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc, integral_const_mul]
  refine ⟨i, ⟨fun s => c * N.value s, fun s hs => analyticAt_const.mul (N.analytic s hs), ?_⟩, fun s => ?_⟩
  · obtain ⟨b, hb⟩ := N.eq_on_right
    exact ⟨b, fun s hs => by rw [hi s, hb s hs, mul_assoc]⟩
  · change c * N.value s = (c • p).eval s
    rw [hN, smul_eq_C_mul, eval_mul, eval_C]

/-- Polynomial normalizations of the ordinary unequal tests at an irreducible real pair,
together with pointwise coverage, give a finite sum of normalized values equal to one. -/
def RealUnequalFiniteSumFromPolynomialsStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (d e : List RealBlock),
    IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d) →
    IsIrreducibleGKModule (realStandardRep (t + 1) e) (realStandardLie (t + 1) e) →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData t),
    let I := realOrdinaryUnequalTest h d e a D
    let L := realPairLFactor d e
    (∀ i, ∃ (p : ℂ[X]) (N : OrdinaryIntegralNormalization (I i) (fun s => (L.denominator s)⁻¹)),
      ∀ s, N.value s = p.eval s) →
    HasCoveringOrdinaryNormalizations I L →
    HasFiniteOrdinaryNormalizationSum I L

set_option maxHeartbeats 1200000 in
theorem realUnequalFiniteSumFromPolynomials : RealUnequalFiniteSumFromPolynomialsStatement := by
  intro r t h d e hD hE a D I L hPoly hCover
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ s : ℂ, b < s.re → L.denominator s ≠ 0 :=
    ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks d e)
  refine ordinaryPolynomialGeneration I L ?_ (fun c p hp => realUnequalPolynomial_smul h a D c hp) ?_
  · intro s
    obtain ⟨i, N, hN⟩ := hCover s
    obtain ⟨p, M, hM⟩ := hPoly i
    have he := N.value_eq_of_factor_ne_zero M ⟨b, fun z hz => inv_ne_zero (hb z hz)⟩
    rw [he, hM] at hN
    exact ⟨p, ⟨i, M, hM⟩, hN⟩
  · intro p hp
    obtain ⟨⟨W, V⟩, N, hN⟩ := hp
    obtain ⟨p₁, N₁, hN₁⟩ := hPoly (firstRightDerivative W, V)
    obtain ⟨p₂, N₂, hN₂⟩ := hPoly (W, firstRightDerivative V)
    obtain ⟨b₀, hb₀⟩ := unequalIntegral_spectralDerivative h a D hD hE W V
    obtain ⟨bI, hI⟩ := N.eq_on_right
    obtain ⟨b₁, h₁⟩ := N₁.eq_on_right
    obtain ⟨b₂, h₂⟩ := N₂.eq_on_right
    let B := max b (max b₀ (max bI (max b₁ b₂)))
    let γ : ℂ := ((r - t : ℕ) : ℂ) / 2
    let q : ℂ[X] := γ • p - (p₁ + p₂)
    have hpq : X * p = q := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hInf : (Complex.ofReal '' Ioi B).Infinite :=
        (Set.Ioi_infinite B).image Complex.ofReal_injective.injOn
      apply hInf.mono
      rintro z ⟨x, hx, rfl⟩
      let s : ℂ := x
      have hs : B < s.re := by simpa only [s, Complex.ofReal_re, mem_Ioi] using hx
      have hmax := (le_max_right b _).trans_lt hs
      have hmax' := (le_max_right b₀ _).trans_lt hmax
      have hmax'' := (le_max_right bI _).trans_lt hmax'
      have h₀ := hI s ((le_max_left bI _).trans_lt hmax')
      have h₁' := h₁ s ((le_max_left b₁ b₂).trans_lt hmax'')
      have h₂' := h₂ s ((le_max_right b₁ b₂).trans_lt hmax'')
      have hderiv := hb₀ s ((le_max_left b₀ _).trans_lt hmax)
      change I (firstRightDerivative W, V) s + I (W, firstRightDerivative V) s =
        (-(s - γ)) * I (W, V) s at hderiv
      rw [h₁', h₂', h₀, hN₁, hN₂, hN, ← add_mul, ← mul_assoc] at hderiv
      have he := mul_right_cancel₀ (inv_ne_zero (hb s ((le_max_left b _).trans_lt hs))) hderiv
      change (X * p).eval s = q.eval s
      simp only [q, eval_sub, smul_eq_C_mul, eval_mul, eval_C, eval_add, eval_X]
      linear_combination he
    rw [hpq]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, N, hN⟩))
      (Submodule.add_mem _ (Submodule.subset_span ⟨_, N₁, hN₁⟩)
        (Submodule.subset_span ⟨_, N₂, hN₂⟩))

end Langlands.Global.RankinSelbergGlobal.RealUnequalSpectralMultiplication
