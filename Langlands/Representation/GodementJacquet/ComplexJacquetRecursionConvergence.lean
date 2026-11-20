import Langlands.Representation.GodementJacquet.ComplexJacquetRecursionLogBounds
import Langlands.Representation.GodementJacquet.ComplexJacquetRecursionWeil
import Langlands.Representation.GodementJacquet.ComplexMatrixHaar

/-! # Absolute convergence of the complex Jacquet recursion -/

noncomputable section

open MeasureTheory Topology
open scoped Matrix.Norms.Elementwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (lastRow continuous_lastRow)
open Langlands.RankinSelberg.GLDeterminantDensity
open Langlands.Global.RankinSelbergGlobal hiding detPower
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "I" => Fin m
local notation "H" => GeneralLinear m ℂ
local notation "G" => GeneralLinear n ℂ
local notation "U" => upperUnipotent m ℂ
local notation "M" => Matrix I I ℂ
local notation "R" => Matrix I (Fin n) ℂ
local notation "sm" => ((m : ℕ) : ℂ) / 2
local notation "sn" => ((n : ℕ) : ℂ) / 2

private theorem continuous_jacquetDetWeight (d : ComplexCharacterData)
    (j : ℕ) (s : ℂ) :
    Continuous (fun k : GeneralLinear j ℂ =>
      complexJacquetDetWeight d.character.toMonoidHom k s) := by
  have hdet : Continuous (fun k : GeneralLinear j ℂ => k.val.det) :=
    Units.continuous_val.comp Matrix.GeneralLinearGroup.continuous_det
  have hlog : Continuous (fun k : GeneralLinear j ℂ =>
      Real.log (complexNormalizedAbs k.val.det)) :=
    (hdet.norm.pow 2).log fun k => (complexNormalizedAbs_det_pos k).ne'
  exact (Units.continuous_val.comp (d.character.continuous.comp
    Matrix.GeneralLinearGroup.continuous_det)).mul
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog)))

private theorem norm_jacquetDetWeight (d : ComplexCharacterData) (k : H) (s : ℂ) :
    ‖complexJacquetDetWeight d.character.toMonoidHom k s‖ =
      Real.exp ((d.exponent.re + s.re) * Real.log (complexNormalizedAbs k.val.det)) := by
  let z := determinant k
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hχ : ‖(d.character z : ℂ)‖ = Real.exp
      (d.exponent.re * Real.log (complexNormalizedAbs k.val.det)) := by
    rw [d.character_eq, norm_mul, norm_zpow, norm_div, Complex.norm_real, norm_norm,
      div_self hz.ne', one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz,
      Real.rpow_def_of_pos hz]
    change Real.exp (Real.log ‖(z : ℂ)‖ * (2 * d.exponent).re) =
      Real.exp (d.exponent.re * Real.log (‖(z : ℂ)‖ ^ 2))
    congr 1
    rw [Real.log_pow, Complex.mul_re]
    norm_num
    ring
  change ‖(d.character z : ℂ) * detPower complexNormalizedAbs k s‖ = _
  rw [norm_mul, hχ, detPower, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, ← Real.exp_add, add_mul]

private theorem coe_matrixWeight_eq_exp (k : H) :
    (matrixWeight m complexAbsHom k.val : ℝ) =
      Real.exp (-(m : ℝ) * Real.log (complexNormalizedAbs k.val.det)) := by
  have h := complexNormalizedAbs_det_pos k
  rw [mul_comm, ← Real.rpow_def_of_pos h, show (m : ℝ) = ((m : ℕ) : ℝ) by norm_cast,
    Real.rpow_neg h.le, Real.rpow_natCast]
  simp only [matrixWeight, NNReal.coe_pow, NNReal.coe_inv, coe_complexAbsHom,
    complexNormalizedAbs, inv_pow]

private theorem exists_jacquetKernel_majorant (a : ℂˣ) (Φ : SchwartzMap R ℂ)
    (d : ComplexCharacterData) {W : H → ℂ}
    (hU : ∀ (u : U) (k : H), ‖W (u.val * k)‖ = ‖W k‖)
    (hW : HasSimpleRootLogBound W) (g : G) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : H,
      ‖matrixWeight m complexAbsHom (k⁻¹).val •
          complexJacquetRecursionGroupKernel a Φ W d.character.toMonoidHom g k‖ ≤
        C * ((1 + ‖(k⁻¹).val‖) ^ N)⁻¹ := by
  let t := d.exponent.re + (sn - 1).re - (m : ℝ)
  let Φg := complexRectangularTranslate (1 : H) g Φ
  have hΦg : (Φg : R → ℂ) = fun X => Φ (X * g.val) :=
    funext fun X => by simp [Φg, complexRectangularTranslate_apply]
  obtain ⟨b, B, hB, hbound⟩ := exists_complexJacquet_weighted_bound hU hW t
  obtain ⟨J, hJ, hFourier⟩ := exists_norm_complexLastColumnFourier_le (-a) Φg (b + N) b
  let A := ‖complexJacquetDetWeight d.character.toMonoidHom g sm‖
  refine ⟨A * J * B, by positivity, fun k => ?_⟩
  let P := 1 + ‖(k⁻¹).val‖
  let Q := 1 + ‖lastRow k‖
  let L := Real.log (complexNormalizedAbs (k⁻¹).val.det)
  have hP : 0 < P := by dsimp [P]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hnorm :
      ‖matrixWeight m complexAbsHom (k⁻¹).val •
          complexJacquetRecursionGroupKernel a Φ W d.character.toMonoidHom g k‖ =
        A * ‖complexLastColumnFourier (-a) Φg (k⁻¹).val (lastRow k)‖ *
          (‖W k‖ * Real.exp (t * L)) := by
    rw [NNReal.smul_def, norm_smul, Real.norm_of_nonneg (NNReal.coe_nonneg _),
      coe_matrixWeight_eq_exp, complexJacquetRecursionGroupKernel, ← hΦg, norm_mul,
      norm_mul, norm_mul, norm_jacquetDetWeight d k⁻¹ (sn - 1)]
    change Real.exp (-(m : ℝ) * L) *
      (A * ‖complexLastColumnFourier (-a) Φg (k⁻¹).val (lastRow k)‖ * ‖W k‖ *
        Real.exp ((d.exponent.re + (sn - 1).re) * L)) = _
    rw [show t * L = -(m : ℝ) * L + (d.exponent.re + (sn - 1).re) * L by dsimp [t]; ring,
      Real.exp_add]
    ring
  rw [hnorm]
  calc
    _ ≤ (A * (J / (P ^ (b + N) * Q ^ b))) * (B * (P ^ b * Q ^ b)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFourier (k⁻¹).val (lastRow k)) (norm_nonneg _))
        (hbound k) (by positivity) (by positivity)
    _ = _ := by
      change A * (J / (P ^ (b + N) * Q ^ b)) * (B * (P ^ b * Q ^ b)) =
        A * J * B * (P ^ N)⁻¹
      rw [pow_add]
      field_simp [hP.ne', hQ.ne']

/-- For data with simple-root decay the last-column Fourier formula is
absolutely convergent at every fixed inducing exponent. -/
theorem integrable_complexJacquetRecursionGroupKernel (a : ℂˣ)
    (D : ComplexQuotientMeasureData r) (Φ : SchwartzMap R ℂ)
    (d : ComplexCharacterData) {W : H → ℂ} (hWcont : Continuous W)
    (hU : ∀ (u : U) (k : H),
      W (u.val * k) = traceCharacter a (unipotentFourierSum r u) * W k)
    (hW : HasSimpleRootLogBound W) (g : G) :
    Integrable (complexJacquetRecursionGroupKernel a Φ W d.character.toMonoidHom g) D.groupHaar := by
  let : FiniteDimensional ℝ M := inferInstanceAs (FiniteDimensional ℝ (I → I → ℂ))
  let : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (I → I → ℂ))
  let : BorelSpace M := inferInstanceAs (BorelSpace (I → I → ℂ))
  let μ : Measure M := Measure.addHaarMeasure (Classical.arbitrary (TopologicalSpace.PositiveCompacts M))
  let : μ.IsAddHaarMeasure := Measure.isAddHaarMeasure_addHaarMeasure _
  let e := RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := e.locallyCompactSpace
  let : SecondCountableTopology H := e.secondCountableTopology
  let : TopologicalSpace.PseudoMetrizableSpace H := e.isInducing.pseudoMetrizableSpace
  let μH := complexMatrixHaar m μ
  let : μH.IsHaarMeasure := complexMatrixHaar_isHaar m μ
  let : μH.IsMulRightInvariant := complexMatrixHaar_isMulRightInvariant m μ
  let : μH.IsInvInvariant := Unfolding.isInvInvariant_of_isMulRightInvariant μH
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let K := complexJacquetRecursionGroupKernel a Φ W d.character.toMonoidHom g
  let Φg := complexRectangularTranslate (1 : H) g Φ
  have hΦg : (Φg : R → ℂ) = fun X => Φ (X * g.val) :=
    funext fun X => by simp [Φg, complexRectangularTranslate_apply]
  have hK : Continuous K := by
    unfold K complexJacquetRecursionGroupKernel
    rw [← hΦg]
    exact ((continuous_const.mul ((continuous_complexLastColumnFourier (-a) Φg).comp
      ((Units.continuous_val.comp continuous_inv).prodMk continuous_lastRow))).mul hWcont).mul
      ((continuous_jacquetDetWeight d m (sn - 1)).comp continuous_inv)
  have hnorm (u : U) (k : H) : ‖W (u.val * k)‖ = ‖W k‖ := by
    rw [hU, norm_mul, norm_traceCharacter, one_mul]
  obtain ⟨C, _, hbound⟩ :=
    exists_jacquetKernel_majorant a Φ d hnorm hW g μ.integrablePower
  let F : M → ℂ := Function.extend (Units.val : H → M) (fun k => K k⁻¹) (fun _ => 0)
  have hF : Measurable F := e.measurableEmbedding.measurable_extend
    (hK.comp continuous_inv).measurable measurable_const
  have hF_val (k : H) : F k.val = K k⁻¹ := e.injective.extend_apply _ _ _
  have hWeight : Measurable (fun X : M => matrixWeight m complexAbsHom X) :=
    measurable_matrixWeight m complexAbsHom continuous_complexAbsHom
  have hMajor : Integrable (fun X : M => ((1 + ‖X‖) ^ μ.integrablePower)⁻¹) μ := by
    simpa only [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖(_ : M)‖), Real.rpow_natCast] using
      μ.integrable_pow_neg_integrablePower
  have hI : Integrable (fun k : H => K k⁻¹) μH := by
    simp_rw [← hF_val]
    apply (integrable_weightedRestriction_iff m complexAbsHom continuous_complexAbsHom μ F).2
    refine ((hMajor.const_mul C).mono_measure Measure.restrict_le_self).mono'
      ((NNReal.continuous_coe.measurable.comp hWeight).smul hF).aestronglyMeasurable ?_
    apply (ae_restrict_iff' e.measurableEmbedding.measurableSet_range).2
    refine ae_of_all _ fun X hX => ?_
    obtain ⟨k, rfl⟩ := hX
    rw [hF_val]
    simpa only [inv_inv] using hbound k⁻¹
  have hI' : Integrable K μH := by simpa only [inv_inv] using hI.comp_inv
  rw [Measure.isMulLeftInvariant_eq_smul D.groupHaar μH]
  exact hI'.smul_measure_nnreal

/-- The quotient and group recursions agree for all fixed parameters
under the simple-root decay estimate on the smaller coefficient. -/
theorem complexJacquetRecursion_eq_group_of_simpleRootLogBound (a : ℂˣ)
    (D : ComplexQuotientMeasureData r) (Φ : SchwartzMap R ℂ)
    (d : ComplexCharacterData) {W : H → ℂ} (hWcont : Continuous W)
    (hU : ∀ (u : U) (k : H),
      W (u.val * k) = traceCharacter a (unipotentFourierSum r u) * W k)
    (hW : HasSimpleRootLogBound W) (g : G) :
    complexJacquetRecursion a D Φ W d.character.toMonoidHom g =
      ∫ k : H, complexJacquetRecursionGroupKernel a Φ W d.character.toMonoidHom g k ∂D.groupHaar :=
  complexJacquetRecursion_eq_integral_group a D Φ W _ hU g
    (integrable_complexJacquetRecursionGroupKernel a D Φ d hWcont hU hW g)

/-- Fixed-parameter convergence and duality for the recursive kernel, on a
smaller coefficient satisfying the simple-root decay estimate. -/
def ComplexJacquetRecursionFixedParameterStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (Φ : SchwartzMap (Matrix (Fin (r + 1)) (Fin ((r + 1) + 1)) ℂ) ℂ)
    (d : ComplexCharacterData) (W : GeneralLinear (r + 1) ℂ → ℂ), Continuous W →
    (∀ (u : upperUnipotent (r + 1) ℂ) (k : GeneralLinear (r + 1) ℂ),
      W (u.val * k) = traceCharacter a (unipotentFourierSum r u) * W k) →
    HasSimpleRootLogBound W →
    ∀ g : GeneralLinear ((r + 1) + 1) ℂ,
      Integrable (complexJacquetRecursionGroupKernel a Φ W d.character.toMonoidHom g)
        D.groupHaar ∧
      complexJacquetRecursion a D Φ W d.character.toMonoidHom g =
        (∫ k, complexJacquetRecursionGroupKernel a Φ W d.character.toMonoidHom g k ∂D.groupHaar) ∧
      complexJacquetRecursion a D Φ W d.character.toMonoidHom
          (weylInverseTranspose ((r + 1) + 1) ℂ g) =
        ((d.character (-1) : ℂˣ) : ℂ) ^ (r + 1) *
          complexJacquetRecursion (-a) D (complexRectangularFourier (-a) Φ)
            (Whittaker.dualFunction r W) (d.character.toMonoidHom.comp invMonoidHom) g

theorem complexJacquetRecursionFixedParameter : ComplexJacquetRecursionFixedParameterStatement := by
  intro r a D Φ d W hWcont hU hW g
  exact ⟨integrable_complexJacquetRecursionGroupKernel a D Φ d hWcont hU hW g,
    complexJacquetRecursion_eq_group_of_simpleRootLogBound a D Φ d hWcont hU hW g,
    complexJacquetRecursion_dual a D Φ W d.character.toMonoidHom hU g⟩

end Langlands.GodementJacquet
