import Langlands.Global.RankinSelberg.ComplexGapRetainedNormalization
import Langlands.Global.RankinSelberg.ComplexGapNormalizedWeighted
import Langlands.Representation.RankinSelberg.TwistInvariance

/-! # The retained normalization at an embedded leading unitary -/

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapRetained

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz)
open Langlands.LocalFactor.Archimedean
open Langlands.QuotientIntegration (rightTranslate rightTranslate_mk)
open Langlands.RankinSelberg (LeftUnipotentQuotient det_rankInclusion)
open ComplexGapNormalizedWeighted (padGL_eq_rankInclusion)
open ComplexGapRankCoordinates (rankLT)
open ComplexGapSeparatedKernels (detPower_mul)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSquareReflection (leadingSquareTest leadingSquareTest_group)
open ComplexGodement (characterWeight normPower)
open ComplexGodementPaddedRestriction (normPower_determinant)
open ComplexJacquet (HasSquareConvolutionTrace complexJacquetMatrixIntegrand)
open ComplexUnequalFamily (HasLeftCharacter ordinaryKernel_mk)
open ComplexUnequalWeightedTranslation (hasLeftCharacter_of_rightTranslate)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "Rank" => t + 1 + q + 1
local notation "LowerIndex" => t + 1 + q
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "H" => G Small
local notation "Mat" => Matrix (Fin Small) (Fin Small) ℂ
local notation "K" => unitaryCompact ℂ Small
local notation "Q" => LeftUnipotentQuotient t ℂ
local notation "ν" => complexGeneralLinearHaar Small
local notation "ρ" => ArchimedeanLocal.translateFunction
local notation "Incl" => (rankInclusion (R := ℂ) (q + 1) : H →* G Rank)
local notation "KF[" es "]" => complexStandardKFinite Small es

private theorem unitary_detPower (u : K) (s : ℂ) : ArchimedeanLocal.detPower complexNormalizedAbs u.val s = 1 := by
  have h : complexNormalizedAbs u.val.val.det = 1 := by
    have hu := normSqC_det_unitary u
    change ((‖u.val.val.det‖ ^ 2 : ℝ) : ℂ) = 1 at hu
    exact_mod_cast hu
  simp only [ArchimedeanLocal.detPower, h, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

private theorem unitary_characterWeight (u : K) (d : ComplexCharacterData) (s : ℂ) :
    characterWeight d s (determinant u.val) = (d.character (determinant u.val) : ℂ) := by
  change (d.character (determinant u.val) : ℂ) * normSqC u.val.val.det ^ s = _
  rw [normSqC_det_unitary u, Complex.one_cpow, mul_one]

set_option maxHeartbeats 1300000 in
private theorem squareTrace_unitary (d : ComplexCharacterData) (Φ : EntrySchwartz Rank Small)
    (Ψ : 𝓢(Mat, ℂ)) (hΨ : ∀ X : Mat, leadingSquareTest t q 1 Φ X = Ψ X)
    (V : H → ℂ) (s : ℂ) (u : K) (x : H) :
    let c := (d.character (determinant u.val) : ℂ)
    (∫ z, squareKernel d (leadingSquareTest t q (Incl u.val) Φ) (fun g => V (x * g)) s z ∂ν) =
      c⁻¹ * ∫ z, squareKernel d Ψ (fun g => V ((x * u.val⁻¹) * g)) s z ∂ν := by
  intro c
  let J := squareKernel d Ψ (fun g => V ((x * u.val⁻¹) * g)) s
  let T := characterWeight d ((t : ℂ) / 2 + s)
  have hTest (z : H) : leadingSquareTest t q (Incl u.val) Φ z.val = Ψ (u.val * z).val := by
    calc
      _ = Φ (ComplexGapDualArguments.leading Small q (Incl u.val * Incl z)) := leadingSquareTest_group t q _ Φ z
      _ = Φ (ComplexGapDualArguments.leading Small q (1 * Incl (u.val * z))) := by rw [one_mul, map_mul]
      _ = _ := (leadingSquareTest_group t q 1 Φ (u.val * z)).symm.trans (hΨ _)
  have hc : c ≠ 0 := Units.ne_zero _
  have hT (z : H) : T (determinant (u.val * z)) = c * T (determinant z) := by
    rw [map_mul determinant, map_mul T]
    exact congrArg (· * T (determinant z)) (unitary_characterWeight t u d _)
  have hJ (z : H) : J (u.val * z) = Ψ (u.val * z).val * (c * T (determinant z)) * V (x * z) := by
    change Ψ (u.val * z).val * T (determinant (u.val * z)) * V ((x * u.val⁻¹) * (u.val * z)) = _
    rw [hT, mul_assoc x, inv_mul_cancel_left]
  have he (z : H) : squareKernel d (leadingSquareTest t q (Incl u.val) Φ) (fun g => V (x * g)) s z = c⁻¹ * J (u.val * z) := by
    change leadingSquareTest t q (Incl u.val) Φ z.val * T (determinant z) * V (x * z) = _
    rw [hTest, hJ]
    field_simp [hc]
  calc
    _ = ∫ z : H, c⁻¹ * J (u.val * z) ∂ν := integral_congr_ae (ae_of_all _ he)
    _ = _ := by rw [integral_const_mul, integral_mul_left_eq_self (μ := ν) J u.val]

private theorem lowerIntegral_unitary (a : ℂˣ) {ds es : List ComplexCharacterData} (D : ComplexQuotientMeasureData t)
    (W : complexWhittakerModel LowerIndex ds (-a)) (V : complexWhittakerModel t es a) (s : ℂ) (u : K) (c : ℂ) :
    complexUnequalIntegral (rankLT t q) D (ρ (Incl u.val)⁻¹ W.val) (fun x => c * V.val (x * u.val⁻¹)) s =
      c * complexUnequalIntegral (rankLT t q) D W.val V.val s := by
  let h := rankLT t q
  let U := Langlands.GeneralLinear.upperUnipotent Small ℂ
  let T := rightTranslate U u.val⁻¹
  let J := complexUnequalIntegrand h W.val V.val s
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  have hT := D.compatible.right_invariant u.val⁻¹
  change (∫ p, complexUnequalIntegrand h (ρ (Incl u.val)⁻¹ W.val) (fun x => c * V.val (x * u.val⁻¹)) s p ∂D.measure) =
    c * ∫ p, J p ∂D.measure
  rw [← hT.integral_comp T.toMeasurableEquiv.measurableEmbedding J, ← integral_const_mul]
  apply integral_congr_ae (ae_of_all _ fun p => ?_)
  let g := p.out
  have hP : (Quotient.mk _ g : Q) = p := Quotient.out_eq p
  rw [← hP]
  change _ = c * J (rightTranslate U u.val⁻¹ (Quotient.mk _ g))
  rw [rightTranslate_mk]
  have hW : HasLeftCharacter (-a) W.val := fun n x => complexWhittakerModel_left_equivariant W.2 n.val n.2 x
  have hV : HasLeftCharacter (-(-a)) V.val := by
    rw [neg_neg]
    exact fun n x => complexWhittakerModel_left_equivariant V.2 n.val n.2 x
  have hV' : HasLeftCharacter (-(-a)) (fun x => c * V.val (x * u.val⁻¹)) := by
    intro n x
    change c * V.val ((n.val * x) * u.val⁻¹) = complexWhittakerCharacter (-(-a)) n.val * (c * V.val (x * u.val⁻¹))
    rw [mul_assoc, hV]
    ring
  rw [ordinaryKernel_mk h (hasLeftCharacter_of_rightTranslate W (Incl u.val)⁻¹) hV',
    show J (Quotient.mk _ (g * u.val⁻¹)) = complexUnequalIntegrand h W.val V.val s (Quotient.mk _ (g * u.val⁻¹)) from rfl,
    ordinaryKernel_mk h hW hV]
  have hPad (x : H) : padGL (Nat.succ_le_succ h.le) x = Incl x := padGL_eq_rankInclusion Small q x
  rw [hPad g, hPad (g * u.val⁻¹), ← map_inv Incl]
  simp only [ArchimedeanLocal.translateFunction, ← map_mul Incl]
  have hDet := unitary_detPower t u⁻¹ (s - ((LowerIndex - t : ℕ) : ℂ) / 2)
  change ArchimedeanLocal.detPower complexNormalizedAbs u.val⁻¹ (s - ((LowerIndex - t : ℕ) : ℂ) / 2) = 1 at hDet
  simp only [detPower_mul, hDet, mul_one]
  ring

private theorem matrixIntegrand_square (d : ComplexCharacterData) (Ψ : 𝓢(Mat, ℂ))
    (V : H → ℂ) (s : ℂ) (z : H) :
    complexJacquetMatrixIntegrand d V Ψ s z = squareKernel d Ψ V s z := by
  change Ψ z.val * (d.character (determinant z) : ℂ) *
      ArchimedeanLocal.detPower complexNormalizedAbs z (s + (t : ℂ) / 2) * V z =
    Ψ z.val * ((d.character (determinant z) : ℂ) * normPower ((t : ℂ) / 2 + s) (determinant z)) * V z
  rw [normPower_determinant, add_comm s]
  ring

/-- The retained family, multiplied by the adjoining determinant character, has the same
value at each embedded leading unitary as the unshifted lower normalization of the
reference square convolution. -/
def ComplexGapUnitaryFiberStatement : Prop :=
  ∀ (a : ℂˣ) (d : ComplexCharacterData) (ds : List ComplexCharacterData) (e : Fin Small → ComplexCharacterData)
    (D : ComplexQuotientMeasureData t),
    let es := List.ofFn e
    ∀ (W : complexWhittakerModel LowerIndex ds (-a)) (B : KF[es] →ₗ[ℂ] (H → ℂ)),
      IsComplexWhittakerIntertwiner t es a B →
    ∀ (A : KF[es] →ₗ[ℂ] (ℂ → ℂ)),
      (∀ v, Differentiable ℂ (A v) ∧ ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexUnequalIntegrand (rankLT t q) W.val (B v) s) D.measure ∧
        A v s = (complexPairLFactor ds es).denominator s * complexUnequalIntegral (rankLT t q) D W.val (B v) s) →
    ∀ (Φ : EntrySchwartz Rank Small) (Ψ : 𝓢(Mat, ℂ)),
      (∀ X : Mat, leadingSquareTest t q 1 Φ X = Ψ X) →
    ∀ (f : KF[es]) (F : ℂ → KF[es]), HasSquareConvolutionTrace ν d e B Ψ f F →
    ∀ (u : K) (Y : ℂ → KF[es]) (J : ℂ → ℂ), Differentiable ℂ J →
      (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        (∀ x : H, (complexPairLFactor [d] es).denominator s *
          (∫ z, squareKernel d (leadingSquareTest t q (Incl u.val) Φ) (fun g => B f (x * g)) s z ∂ν) = B (Y s) x) ∧
        J s = (complexPairLFactor ds es).denominator s * complexUnequalIntegral (rankLT t q) D (ρ (Incl u.val)⁻¹ W.val) (B (Y s)) s) →
      ∀ s : ℂ, (d.character (determinant (Incl u.val)) : ℂ) * J s = A (F s) s

set_option maxHeartbeats 1800000 in
theorem complexGapUnitaryFiber : ComplexGapUnitaryFiberStatement t q := by
  intro a d ds e D es W B hB A hA Φ Ψ hΨ f F hF u Y J hJ ⟨σ, hσ⟩
  obtain ⟨l, p, v, hv⟩ := hF.1
  obtain ⟨τ, hτ⟩ := hF.2
  choose b hb using fun i : Fin l => (hA (v i)).2
  obtain ⟨c, hc⟩ := (finite_range b).bddAbove
  let σ₀ := max (max σ τ) c
  let χ := (d.character (determinant u.val) : ℂ)
  have hχ₀ : χ ≠ 0 := Units.ne_zero _
  have hχ : (d.character (determinant (Incl u.val)) : ℂ) = χ := by
    have he : determinant (Incl u.val) = determinant u.val := Units.ext (det_rankInclusion _ _)
    rw [he]
  rw [hχ]
  have hFun : Differentiable ℂ (fun s => A (F s) s) := by
    simp_rw [hv, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Differentiable.fun_sum fun i _ => (p i).differentiable.mul (hA (v i)).1
  have hRight (s : ℂ) (hs : σ₀ < s.re) : χ * J s = A (F s) s := by
    have hs₁ := (le_max_left σ τ).trans_lt ((le_max_left (max σ τ) c).trans_lt hs)
    have hs₂ := (le_max_right σ τ).trans_lt ((le_max_left (max σ τ) c).trans_lt hs)
    have hj (i : Fin l) := hb i s ((hc (mem_range_self i)).trans_lt ((le_max_right (max σ τ) c).trans_lt hs))
    let V : complexWhittakerModel t es a :=
      ⟨B (F s), Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨F s, rfl⟩)⟩
    have hY : B (Y s) = fun x => χ⁻¹ * V.val (x * u.val⁻¹) := by
      funext x
      rw [← (hσ s hs₁).1 x, squareTrace_unitary t q d Φ Ψ hΨ (B f) s u x, ← mul_left_comm,
        show V.val (x * u.val⁻¹) = B (F s) (x * u.val⁻¹) from rfl, hτ s hs₂]
      simp_rw [matrixIntegrand_square]
      rfl
    rw [(hσ s hs₁).2, hY, lowerIntegral_unitary t q a D W V s u χ⁻¹]
    rw [mul_left_comm χ, ← mul_assoc χ, mul_inv_cancel₀ hχ₀, one_mul]
    have he (z : Q) : complexUnequalIntegrand (rankLT t q) W.val (B (F s)) s z =
        ∑ i, (p i).eval s * complexUnequalIntegrand (rankLT t q) W.val (B (v i)) s z := by
      simp only [hv, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    change (complexPairLFactor ds es).denominator s *
      (∫ z, complexUnequalIntegrand (rankLT t q) W.val (B (F s)) s z ∂D.measure) = _
    simp_rw [he]
    have hi (i : Fin l) (_ : i ∈ Finset.univ) : Integrable
        (fun x => (p i).eval s * complexUnequalIntegrand (rankLT t q) W.val (B (v i)) s x) D.measure :=
      (hj i).1.const_mul _
    rw [integral_finsetSum _ hi, hv, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, ← mul_left_comm, map_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg ((p i).eval s * ·) (hj i).2.symm
  let z : ℂ := ((σ₀ + 1 : ℝ) : ℂ)
  have h := AnalyticOnNhd.eq_of_eventuallyEq (f := fun s => χ * J s) (g := fun s => A (F s) s)
    (fun w _ => ((hJ.const_mul χ).analyticAt w)) (fun w _ => hFun.analyticAt w) (z₀ := z) (by
      apply (isOpen_lt continuous_const Complex.continuous_re).eventually_mem
        (show σ₀ < z.re by rw [show z.re = σ₀ + 1 from Complex.ofReal_re _]; linarith) |>.mono
      exact hRight)
  exact congrFun h

end Langlands.Global.RankinSelbergGlobal.ComplexGapRetained
