import Langlands.Global.RankinSelberg.ComplexLocalEqualFamily
import Langlands.Global.RankinSelberg.ComplexWhittakerTranslatedMellin
import Langlands.Representation.GodementJacquet.ComplexJacquetDeterminantWeight
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Spectral multiplication for ordinary complex equal-rank integrals -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexEqualSpectralMultiplication

open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean
open Langlands.QuotientIntegration (rightTranslate_mk)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal
open ComplexCharacterChange (model_mul_scalar centralCharacter coe_centralCharacter
  complexEqualIntegrand_mk model_pair_invariant)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexJacquet (equalFamily_halfPlaneDomination_of_lastRowBound equalFamily_kernel_continuous)
open ComplexLastRowSchwartz (complexLastRowSchwartz)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)
open ComplexUnequalFamily (HasLeftCharacter)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Row" => Fin (r + 1) → ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "row" => Langlands.RankinSelberg.lastRow
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

/-- The radial derivative of a row Schwartz test, given by its differential
applied to the row itself. -/
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

private theorem lastRow_logTorus_mul (y : Fin (r + 1) → ℝ) (k : K) :
    row (logTorus y * k.val) = Real.exp (y (Fin.last r)) • row k.val := by
  funext j
  change ((logTorus y * k.val).val) (Fin.last r) j = Real.exp (y (Fin.last r)) • k.val.val (Fin.last r) j
  rw [Units.val_mul, logTorus_val, Matrix.diagonal_mul, Complex.real_smul]

private theorem dilatedRowBound (Φ : 𝓢(Row, ℂ)) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-1 : ℝ) 1, ∀ (y : Fin (r + 1) → ℝ) (k : K),
      ‖Φ (Real.exp x • row (logTorus y * k.val))‖ ≤ C * Real.exp (-(M : ℝ) * max (y (Fin.last r)) 0) := by
  obtain ⟨C, hC, hb⟩ := (complexLastRowSchwartz (r := r)) Φ M
  refine ⟨C * Real.exp M, by positivity, fun x hx y k => ?_⟩
  let y' : Fin (r + 1) → ℝ := fun j => x + y j
  have he : Real.exp x • row (logTorus y * k.val) = row (logTorus y' * k.val) := by
    rw [lastRow_logTorus_mul, lastRow_logTorus_mul, smul_smul]
    simp only [y', Real.exp_add]
  rw [he]
  refine (hb y' k).trans ?_
  have hy : max (y (Fin.last r)) 0 ≤ max (y' (Fin.last r)) 0 + 1 := by
    apply max_le
    · have h := le_max_left (y' (Fin.last r)) 0
      dsimp only [y'] at h
      linarith [hx.1]
    · linarith [le_max_right (y' (Fin.last r)) 0]
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  nlinarith [mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]

private def positiveScalar (x : ℝ) : ℂˣ :=
  Units.mk0 (Real.exp x : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')

private theorem character_positiveScalar (d : ComplexCharacterData) (x : ℝ) :
    (d.character (positiveScalar x) : ℂ) = Complex.exp ((x : ℂ) * (2 * d.exponent)) := by
  have hne := Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'
  rw [d.character_eq]
  simp only [positiveScalar, Units.val_mk0, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos x).le,
    div_self hne, one_zpow, one_mul]
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

private theorem centralCharacter_positiveScalar (d : List ComplexCharacterData) (x : ℝ) :
    (centralCharacter d (positiveScalar x) : ℂ) =
      Complex.exp ((x : ℂ) * (2 * (d.map ComplexCharacterData.exponent).sum)) := by
  rw [coe_centralCharacter]
  induction d with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [character_positiveScalar, ih, ← Complex.exp_add]
    congr 1
    ring

private theorem lastRow_mul_positiveScalar (x : ℝ) (g : G) :
    row (g * GeneralLinear.scalar (positiveScalar x)) = Real.exp x • row g := by
  funext j
  change (g.val * Matrix.diagonal (fun _ : Fin (r + 1) => (Real.exp x : ℂ))) (Fin.last r) j =
    Real.exp x • g.val (Fin.last r) j
  rw [Matrix.mul_diagonal, Complex.real_smul, mul_comm]

private theorem detPower_positiveScalar (x : ℝ) (s : ℂ) :
    P (GeneralLinear.scalar (positiveScalar x) : G) s = Complex.exp ((x : ℂ) * (2 * (r + 1) * s)) := by
  change Complex.exp (s * (Real.log (complexNormalizedAbs
    (Matrix.diagonal (fun _ : Fin (r + 1) => (Real.exp x : ℂ))).det) : ℂ)) = _
  simp only [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, complexNormalizedAbs, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), ← pow_mul, Real.log_pow, Real.log_exp,
    Complex.ofReal_mul, Complex.ofReal_natCast, Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  push_cast
  ring

variable {d e : List ComplexCharacterData} {a : ℂˣ} (D : ComplexQuotientMeasureData r)

private def scalarShift (d e : List ComplexCharacterData) (s : ℂ) : ℂ :=
  -2 * ((r + 1) * s + (d.map ComplexCharacterData.exponent).sum + (e.map ComplexCharacterData.exponent).sum)

private theorem equalIntegral_dilatedRow (hd : d.length = r + 1) (he : e.length = r + 1)
    (W : complexWhittakerModel r d a) (V : complexWhittakerModel r e (-a))
    (Φ : 𝓢(Row, ℂ)) (x : ℝ) (s : ℂ) :
    complexEqualIntegral D W.val V.val (fun y => Φ (Real.exp x • y)) s =
      Complex.exp ((x : ℂ) * scalarShift (r := r) d e s) * complexEqualIntegral D W.val V.val Φ s := by
  let u : G := GeneralLinear.scalar (positiveScalar x)
  let E := Langlands.QuotientIntegration.rightTranslate (GeneralLinear.upperUnipotent (r + 1) ℂ) u
  let m := Complex.exp ((x : ℂ) * scalarShift (r := r) d e s)
  have hm : MeasurePreserving E D.measure D.measure := by
    let := D.unipotentHaar_rightInvariant
    exact D.compatible.right_invariant u
  have hK : complexEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s =
      fun q => m * complexEqualIntegrand W.val V.val Φ s (E q) := by
    funext q
    induction q using Quotient.inductionOn with
    | _ g =>
      rw [show E (Quotient.mk _ g) = Quotient.mk _ (g * u) from rightTranslate_mk _ _ _,
        complexEqualIntegrand_mk (model_pair_invariant W.2 V.2),
        complexEqualIntegrand_mk (model_pair_invariant W.2 V.2)]
      rw [show u = GeneralLinear.scalar (positiveScalar x) from rfl,
        lastRow_mul_positiveScalar, model_mul_scalar hd W.2, model_mul_scalar he V.2,
        Langlands.GodementJacquet.detPower_complex_mul, detPower_positiveScalar,
        centralCharacter_positiveScalar, centralCharacter_positiveScalar]
      have hc : m * Complex.exp ((x : ℂ) * (2 * (d.map ComplexCharacterData.exponent).sum)) *
          Complex.exp ((x : ℂ) * (2 * (e.map ComplexCharacterData.exponent).sum)) *
          Complex.exp ((x : ℂ) * (2 * (r + 1) * s)) = 1 := by
        simp only [m, scalarShift, ← Complex.exp_add]
        rw [show (x : ℂ) * (-2 * ((r + 1) * s + (d.map ComplexCharacterData.exponent).sum +
            (e.map ComplexCharacterData.exponent).sum)) +
            (x : ℂ) * (2 * (d.map ComplexCharacterData.exponent).sum) +
            (x : ℂ) * (2 * (e.map ComplexCharacterData.exponent).sum) +
            (x : ℂ) * (2 * (r + 1) * s) = 0 by ring, Complex.exp_zero]
      calc
        _ = (m * Complex.exp ((x : ℂ) * (2 * (d.map ComplexCharacterData.exponent).sum)) *
            Complex.exp ((x : ℂ) * (2 * (e.map ComplexCharacterData.exponent).sum)) *
            Complex.exp ((x : ℂ) * (2 * (r + 1) * s))) * _ := by rw [hc, one_mul]
        _ = _ := by ring
  change (∫ q, complexEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s q ∂D.measure) = _
  rw [hK, integral_const_mul, hm.integral_comp E.measurableEmbedding]
  rfl

private theorem dilatedEqualKernel_domination
    (W : complexWhittakerModel r d a) (V : complexWhittakerModel r e (-a)) (Φ : 𝓢(Row, ℂ)) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re → ∃ M : Q → ℝ, Integrable M D.measure ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q : Q,
        ‖complexEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s q‖ ≤ M q := by
  let S := Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℂ)
  have hBound {ds : List ComplexCharacterData} {b : ℂˣ} (U : complexWhittakerModel r ds b) :
      HasUniformSimpleRootBound S (fun _ => U.val) := by
    obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound U {1} isCompact_singleton
    refine ⟨N, fun J => ?_⟩
    obtain ⟨C, hC, hNb⟩ := hN J
    exact ⟨C, hC, fun _ _ g => by simpa only [mul_one] using hNb 1 (mem_singleton _) g⟩
  have hW : HasLeftCharacter a W.val := fun u g => complexWhittakerModel_left_equivariant W.2 u.val u.2 g
  have hV : HasLeftCharacter (-a) V.val := fun u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g
  obtain ⟨b, hb⟩ := equalFamily_halfPlaneDomination_of_lastRowBound D S (fun _ => W.val)
    (fun _ => V.val) Prod.snd (fun p y => Φ (Real.exp p.1 • y)) (fun _ => hW) (fun _ => hV)
    (hBound W) (hBound V) (by
      intro M
      obtain ⟨C, hC, hCb⟩ := dilatedRowBound Φ M
      exact ⟨C, hC, fun p hp => hCb p.1 hp.1⟩)
  refine ⟨b, fun s hs => ?_⟩
  obtain ⟨M, hM, hMb⟩ := hb s.re
  exact ⟨M, hM, fun x hx q => hMb (x, s) ⟨hx, mem_univ _⟩ hs le_rfl q⟩

private theorem dilatedEqualKernel_measurable
    (W : complexWhittakerModel r d a) (V : complexWhittakerModel r e (-a))
    (Φ : 𝓢(Row, ℂ)) (s : ℂ) (x : ℝ) :
    AEStronglyMeasurable (complexEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s) D.measure := by
  have hW : HasLeftCharacter a W.val := fun u g => complexWhittakerModel_left_equivariant W.2 u.val u.2 g
  have hV : HasLeftCharacter (-a) V.val := fun u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g
  have hWc : Continuous W.val := (contMDiff_of_mem_complexWhittakerModel W.2).continuous
  have hVc : Continuous V.val := (contMDiff_of_mem_complexWhittakerModel V.2).continuous
  have hscale : Continuous (fun y : Row => Real.exp x • y) := by fun_prop
  have hΦ : Continuous (fun y : Row => Φ (Real.exp x • y)) := Φ.continuous.comp hscale
  exact (equalFamily_kernel_continuous hW hV hWc hVc _ hΦ s).aestronglyMeasurable

private theorem hasDerivAt_dilatedEqualKernel
    (W : G → ℂ) (V : G → ℂ) (Φ : 𝓢(Row, ℂ)) (s : ℂ) (x : ℝ) (q : Q) :
    HasDerivAt (fun u : ℝ => complexEqualIntegrand W V (fun y => Φ (Real.exp u • y)) s q)
      (complexEqualIntegrand W V (fun y => radialDerivative Φ (Real.exp x • y)) s q) x := by
  let g : G := q.out
  have h := hasDerivAt_dilatedRow Φ (row g) x
  simpa only [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, g] using
    (h.const_mul (W g * V g)).mul_const (P g s)

/-- The radial derivative of the row test realizes the affine spectral multiplier
from central scalar substitution, on a common right half-plane. -/
def ComplexEqualSpectralMultiplicationStatement : Prop :=
  ∀ (r : ℕ) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = r + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r)
      (W : complexWhittakerModel r d a) (V : complexWhittakerModel r e (-a))
      (Φ : 𝓢((Fin (r + 1) → ℂ), ℂ)), ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      complexEqualIntegral D W.val V.val (radialDerivative Φ) s =
        (-2 * ((r + 1) * s + (d.map ComplexCharacterData.exponent).sum + (e.map ComplexCharacterData.exponent).sum)) *
          complexEqualIntegral D W.val V.val Φ s

set_option maxHeartbeats 1300000 in
theorem complexEqualSpectralMultiplication : ComplexEqualSpectralMultiplicationStatement := by
  intro r d e hd he a D W V Φ
  let U := radialDerivative Φ
  obtain ⟨b, hb⟩ := dilatedEqualKernel_domination D W V Φ
  obtain ⟨b', hb'⟩ := dilatedEqualKernel_domination D W V U
  refine ⟨max b b', fun s hs => ?_⟩
  obtain ⟨M, hM, hMb⟩ := hb s ((le_max_left _ _).trans_lt hs)
  obtain ⟨M', hM', hMb'⟩ := hb' s ((le_max_right _ _).trans_lt hs)
  let F (x : ℝ) := complexEqualIntegrand W.val V.val (fun y => Φ (Real.exp x • y)) s
  let F' (x : ℝ) := complexEqualIntegrand W.val V.val (fun y => U (Real.exp x • y)) s
  have hMeas := dilatedEqualKernel_measurable D W V Φ s
  have hMeas' := dilatedEqualKernel_measurable D W V U s
  have hnb : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hI : Integrable (F 0) D.measure := hM.mono' (hMeas 0) (ae_of_all _ (hMb 0 h0))
  have hDeriv (x : ℝ) (q : LeftUnipotentQuotient r ℂ) : HasDerivAt (fun v => F v q) (F' x q) x :=
    hasDerivAt_dilatedEqualKernel W.val V.val Φ s x q
  obtain ⟨_, hIntDeriv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := M') hnb (Eventually.of_forall hMeas) hI (hMeas' 0)
    (ae_of_all _ fun q x hx => hMb' x hx q) hM' (ae_of_all _ fun q x _ => hDeriv x q)
  let c := scalarShift (r := r) d e s
  have heq : (fun x : ℝ => ∫ q, F x q ∂D.measure) =
      fun x : ℝ => Complex.exp ((x : ℂ) * c) * complexEqualIntegral D W.val V.val Φ s :=
    funext fun x => equalIntegral_dilatedRow D hd he W V Φ x s
  have hOther : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * c) * complexEqualIntegral D W.val V.val Φ s)
      (c * complexEqualIntegral D W.val V.val Φ s) 0 := by
    simpa only [id_eq, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, one_mul] using
      ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const c).cexp).mul_const (complexEqualIntegral D W.val V.val Φ s)
  rw [heq] at hIntDeriv
  simpa only [F', U, Real.exp_zero, one_smul, c, scalarShift, complexEqualIntegral,
    complexEqualIntegrand, ArchimedeanLocal.equalIntegral] using hIntDeriv.unique hOther

end Langlands.Global.RankinSelbergGlobal.ComplexEqualSpectralMultiplication
