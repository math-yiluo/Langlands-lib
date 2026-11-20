import Langlands.Global.RankinSelberg.ComplexJacquetUnipotentMeasure
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Mathlib.MeasureTheory.Integral.Prod

/-! # Absolute convergence of the complex open-cell Jacquet integral -/

noncomputable section

open MeasureTheory
open scoped Manifold Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberConvergence

open GeneralLinear (upperUnipotent weylLong inverseTranspose inverseTranspose_coe
  continuous_inverseTranspose weylLong_mul_self)
open Langlands.Archimedean
open ComplexDuality (exists_diagonalUnits_mul_upperUnipotent_mul_unitary)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_isHaar entryHaar_sigmaFinite
  unipotentProductMeasure_entryHaar transposeReflection transposeReflection_eq
  measurePreserving_transposeReflection)
open ComplexMaximalParabolicIntegration (chartGL JGL_val Jmat iotaGL iotaGL_val
  iotaGL_mem_unitaryCompact iotaGL_mem_upperUnipotent iotaGL_diagonalUnits)
open ComplexPartialJacquet
open Langlands.Shahidi
open HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)

local instance jacquetChamberNMeasurable (m : ℕ) : MeasurableSpace (upperUnipotent m ℂ) := borel _
local instance jacquetChamberNBorel (m : ℕ) : BorelSpace (upperUnipotent m ℂ) := ⟨rfl⟩
local instance jacquetChamberGLMeasurable (m : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear m ℂ) := borel _
local instance jacquetChamberGLBorel (m : ℕ) : BorelSpace (Langlands.GeneralLinear m ℂ) := ⟨rfl⟩

private def groupTranspose {m : ℕ} (g : Langlands.GeneralLinear m ℂ) : Langlands.GeneralLinear m ℂ :=
  inverseTranspose m ℂ g⁻¹

private theorem groupTranspose_val {m : ℕ} (g : Langlands.GeneralLinear m ℂ) :
    (groupTranspose g).val = g.val.transpose := by
  rw [groupTranspose, inverseTranspose_coe, inv_inv]

private theorem continuous_groupTranspose {m : ℕ} :
    Continuous (groupTranspose (m := m)) := (continuous_inverseTranspose m ℂ).comp continuous_inv

private theorem groupTranspose_mul {m : ℕ} (g h : Langlands.GeneralLinear m ℂ) :
    groupTranspose (g * h) = groupTranspose h * groupTranspose g := by
  simp only [groupTranspose, mul_inv_rev, map_mul]

private theorem groupTranspose_lastColumn {m : ℕ} (v : Fin m → ℂ) :
    groupTranspose (lastColumnUpper v).val = chartGL v := by
  apply Units.ext
  rw [groupTranspose_val, chartGL, JGL_val]
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Jmat, lastColumnUpper, Matrix.transpose_apply]
    | cast j => simp [Jmat, lastColumnUpper, Matrix.transpose_apply]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp [Jmat, lastColumnUpper, Matrix.transpose_apply, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j => simp [Jmat, lastColumnUpper, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

private theorem groupTranspose_upperLeft {m : ℕ} (u : upperUnipotent m ℂ) :
    groupTranspose (upperLeftUnipotent u).val = iotaGL (groupTranspose u.val) := by
  apply Units.ext
  rw [groupTranspose_val, iotaGL_val, groupTranspose_val]
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp

private theorem groupTranspose_product {m : ℕ} (p : (upperUnipotent m ℂ) × (Fin m → ℂ)) :
    groupTranspose (unipotentProduct p).val = chartGL p.2 * iotaGL (groupTranspose p.1.val) := by
  rcases p with ⟨u, v⟩
  change groupTranspose ((upperLeftUnipotent u).val * (lastColumnUpper v).val) = _
  rw [groupTranspose_mul, groupTranspose_lastColumn, groupTranspose_upperLeft]

private theorem integrable_chart_iota {m : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}
    (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    {f : Langlands.GeneralLinear (m + 1) ℂ → ℂ} (hf : f ∈ principalSeries ℂ (m + 1) χ)
    (g : Langlands.GeneralLinear m ℂ) :
    Integrable (fun x : Fin m → ℂ => f (chartGL x * iotaGL g)) := by
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  let b : Langlands.GeneralLinear m ℂ := GeneralLinear.Iwasawa.diagonalUnits a * u.val
  let v : upperUnipotent (m + 1) ℂ := ⟨iotaGL u.val, iotaGL_mem_upperUnipotent u⟩
  let z : Fin (m + 1) → ℂˣ := fun i => Fin.lastCases 1 a i
  have hb : iotaGL b = GeneralLinear.Iwasawa.diagonalUnits z * v.val := by
    simp only [b, map_mul, iotaGL_diagonalUnits]
    rfl
  refine ((integrable_comp_vecMul b.det_ne_zero (integrable_chart hχ he hf
    (iotaGL_mem_unitaryCompact hk))).const_mul (principalSeriesCharacter ℂ (m + 1) χ z)).congr
      (ae_of_all _ fun x => ?_)
  change principalSeriesCharacter ℂ (m + 1) χ z *
      f (chartGL (x ᵥ* b.val) * iotaGL k) = f (chartGL x * iotaGL (b * k))
  have hx : chartGL x * iotaGL (b * k) =
      GeneralLinear.Iwasawa.diagonalUnits z * v.val * (chartGL (x ᵥ* b.val) * iotaGL k) := by
    calc
      _ = (chartGL x * iotaGL b) * iotaGL k := by rw [map_mul, mul_assoc]
      _ = _ := by rw [chartGL_mul_iotaGL x b, hb, mul_assoc]
  rw [hx]
  exact (hf.2 z v _).symm

private theorem jacquetStep_ofReal_norm {m : ℕ} {f : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hpos : ∀ g, f g = (‖f g‖ : ℂ)) (g : Langlands.GeneralLinear m ℂ) :
    jacquetStep f g = ((∫ v : Fin m → ℂ, ‖f (chartGL v * iotaGL g)‖ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  exact integral_congr_ae (ae_of_all _ fun v => hpos (chartGL v * iotaGL g))

private theorem jacquetStep_norm {m : ℕ} {f : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hpos : ∀ g, f g = (‖f g‖ : ℂ)) (g : Langlands.GeneralLinear m ℂ) :
    ‖jacquetStep f g‖ = ∫ v : Fin m → ℂ, ‖f (chartGL v * iotaGL g)‖ := by
  rw [jacquetStep_ofReal_norm hpos, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]

private theorem integrable_transposed_positive (μ : AdditiveHaarMeasure ℂ) :
    ∀ (n : ℕ) {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}, IsPhasePower χ e →
    IsStrictlyDominant e (n - 1) → ∀ {f : Langlands.GeneralLinear n ℂ → ℂ},
      f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →
      (∀ g, f g = (‖f g‖ : ℂ)) →
      Integrable (fun u : upperUnipotent n ℂ => f (groupTranspose u.val)) (entryHaar μ n) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  intro n
  induction n with
  | zero =>
    intro χ e hχ he f hf hp
    have : Subsingleton (upperUnipotent 0 ℂ) := ⟨fun u v => by
      apply Subtype.ext
      apply Units.ext
      ext i
      exact Fin.elim0 i⟩
    have : (entryHaar μ 0).IsHaarMeasure := entryHaar_isHaar μ 0
    have : IsFiniteMeasure (entryHaar μ 0) := ⟨isCompact_univ.measure_lt_top⟩
    exact Integrable.of_subsingleton
  | succ m ih =>
    intro χ e hχ he f hf hp
    have : SigmaFinite (entryHaar μ m) := entryHaar_sigmaFinite μ m
    have hm : IsStrictlyDominant e m := by simpa using he
    have hshift : IsStrictlyDominant (fun l => e l - 1 / 2) (m - 1) := by
      intro l hl
      have h := hm l (by omega)
      simp only [Complex.sub_re]
      linarith
    have hstep := ih hχ.shift hshift (jacquetStep_mem hχ hm hf) (fun g => by
      rw [jacquetStep_norm hp, jacquetStep_ofReal_norm hp])
    rw [← unipotentProductMeasure_entryHaar μ m, Langlands.Shahidi.integrable_unipotentProductMeasure_iff]
    simp_rw [groupTranspose_product]
    let c := Measure.addHaarScalarFactor (rowMeasure μ m) volume
    have hc : rowMeasure μ m = c • (volume : Measure (Fin m → ℂ)) :=
      Measure.isAddLeftInvariant_eq_smul (rowMeasure μ m) volume
    have hmeas : AEStronglyMeasurable (fun p : (upperUnipotent m ℂ) × (Fin m → ℂ) =>
        f (chartGL p.2 * iotaGL (groupTranspose p.1.val))) ((entryHaar μ m).prod (rowMeasure μ m)) :=
      (hf.1.1.continuous.comp ((continuous_chartGL.comp continuous_snd).mul
        (continuous_iotaGL.comp (continuous_groupTranspose.comp
          (continuous_subtype_val.comp continuous_fst))))).aestronglyMeasurable
    refine (integrable_prod_iff hmeas).2 ⟨ae_of_all _ fun u => ?_, ?_⟩
    · rw [hc]
      exact (integrable_chart_iota hχ hm hf.1 (groupTranspose u.val)).smul_measure ENNReal.coe_ne_top
    · simp_rw [hc, integral_smul_nnreal_measure, ← jacquetStep_norm hp]
      exact hstep.norm.const_mul (c : ℝ)

/-- The positive character with the specified real exponent at each position. -/
def radialChar (t : ℕ → ℝ) (l : ℕ) (z : ℂˣ) : ℂ :=
  ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (t l : ℂ)

private theorem radialPhasePower (t : ℕ → ℝ) : IsPhasePower (radialChar t) (fun l => (t l : ℂ)) where
  eq l z := by simp [radialChar, ComplexGramFormula.norm_phaseUnit]
  one l := by simp [radialChar]
  norm_phase l z := by simp [radialChar, ComplexGramFormula.norm_phaseUnit]

/-- The positive radial principal-series section with constant unitary restriction one. -/
def sphericalMajorant (m : ℕ) (t : ℕ → ℝ) : Langlands.GeneralLinear m ℂ → ℂ :=
  ComplexPrincipalSeriesExtension.extension (GramFormula.shiftedExponent m (fun l => (t l : ℂ)))
    (fun _ => 1)

theorem sphericalMajorant_mem (m : ℕ) (t : ℕ → ℝ) :
    sphericalMajorant m t ∈ kFiniteFunctions (principalSeries ℂ m (radialChar t))
      (unitaryCompact ℂ m) := by
  apply ComplexPrincipalSeriesExtension.extension_mem_kFiniteFunctions _ (radialPhasePower t).eq
    continuous_const
  · rw [Set.range_const]
    infer_instance
  · intro a k
    simp [principalSeriesCharacter, radialChar, ComplexGramFormula.norm_phaseUnit]

private theorem sphericalMajorant_unitary (m : ℕ) (t : ℕ → ℝ) {k : Langlands.GeneralLinear m ℂ}
    (hk : k ∈ unitaryCompact ℂ m) : sphericalMajorant m t k = 1 := by
  let κ : Matrix.unitaryGroup (Fin m) ℂ := ⟨k.val, hk⟩
  have hκ : Unitary.toUnits κ = k := Units.ext rfl
  rw [← hκ, sphericalMajorant, ComplexPrincipalSeriesExtension.extension_unitary]

theorem sphericalMajorant_ofReal_norm {m : ℕ} (t : ℕ → ℝ) (g : Langlands.GeneralLinear m ℂ) :
    sphericalMajorant m t g = (‖sphericalMajorant m t g‖ : ℂ) := by
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  unfold sphericalMajorant
  rw [ComplexPrincipalSeriesExtension.extension_iwasawa _ _ _ _ hk, mul_one]
  have hexp (i : Fin m) : GramFormula.shiftedExponent m (fun l => (t l : ℂ)) i =
      ((t (i : ℕ) + (((m : ℝ) - 1) / 2 - ((i : ℕ) : ℝ)) : ℝ) : ℂ) := by
    simp only [GramFormula.shiftedExponent, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
  simp_rw [hexp, ← Complex.ofReal_cpow (sq_nonneg _), ← Complex.ofReal_prod, Complex.norm_real,
    Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (sq_nonneg _) _)]

/-- A bound for the right-translated input on the compact group gives a spherical majorant
at every argument in the original upper-Borel coordinates. -/
theorem norm_mul_le_sphericalMajorant {m : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}
    (hχ : IsPhasePower χ e) {f : Langlands.GeneralLinear m ℂ → ℂ}
    (hf : ∀ (a : Fin m → ℂˣ) (u : upperUnipotent m ℂ) (x : Langlands.GeneralLinear m ℂ),
      f (GeneralLinear.Iwasawa.diagonalUnits a * u.val * x) =
        principalSeriesCharacter ℂ m χ a * f x)
    (g : Langlands.GeneralLinear m ℂ) {C : ℝ}
    (hC : ∀ k ∈ unitaryCompact ℂ m, ‖f (k * g)‖ ≤ C) (x : Langlands.GeneralLinear m ℂ) :
    ‖f (x * g)‖ ≤ C * ‖sphericalMajorant m (fun l => (e l).re) x‖ := by
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary x
  let t : ℕ → ℝ := fun l => (e l).re
  have hnorm : ‖principalSeriesCharacter ℂ m χ a‖ = ‖principalSeriesCharacter ℂ m (radialChar t) a‖ := by
    simp only [norm_principalSeriesCharacter hχ, norm_principalSeriesCharacter (radialPhasePower t),
      Complex.ofReal_re, t]
  rw [mul_assoc, hf a u (k * g), (sphericalMajorant_mem m t).1.2 a u k,
    sphericalMajorant_unitary m t hk, mul_one, norm_mul, hnorm]
  exact (mul_le_mul_of_nonneg_left (hC k hk) (norm_nonneg _)).trans (le_of_eq (mul_comm _ _))

/-- The chamber bound only uses continuity and the upper-Borel transformation law. -/
theorem integrable_openCell_of_borelCovariance {r : ℕ} (μ : AdditiveHaarMeasure ℂ)
    {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ} (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e r)
    {f : Langlands.GeneralLinear (r + 1) ℂ → ℂ} (hf : Continuous f)
    (hcov : ∀ (a : Fin (r + 1) → ℂˣ) (u : upperUnipotent (r + 1) ℂ)
      (x : Langlands.GeneralLinear (r + 1) ℂ),
      f (GeneralLinear.Iwasawa.diagonalUnits a * u.val * x) =
        principalSeriesCharacter ℂ (r + 1) χ a * f x)
    (g : Langlands.GeneralLinear (r + 1) ℂ) :
    Integrable (fun u : upperUnipotent (r + 1) ℂ => f (weylLong (r + 1) ℂ * u.val * g))
      (entryHaar μ (r + 1)) := by
  let w := weylLong (r + 1) ℂ
  have hdom : IsStrictlyDominant (fun l => ((e l).re : ℂ)) (r + 1 - 1) := by
    simpa [IsStrictlyDominant] using he
  have hmajor := integrable_transposed_positive μ (r + 1) (radialPhasePower (fun l => (e l).re))
    hdom (sphericalMajorant_mem (r + 1) (fun l => (e l).re)) (sphericalMajorant_ofReal_norm _)
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact (hf.comp (continuous_id.mul
    (continuous_const : Continuous fun _ : Langlands.GeneralLinear (r + 1) ℂ => w * g)))
  apply ((measurePreserving_transposeReflection μ (r + 1)).integrable_comp_emb
    (transposeReflection (r + 1)).measurableEmbedding).mp
  refine ((hmajor.norm.const_mul C).mono' ?_ (ae_of_all _ fun u => ?_))
  · have hc : Continuous (fun u : upperUnipotent (r + 1) ℂ => f (w * u.val * g)) :=
      hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    exact (hc.measurable.comp (transposeReflection (r + 1)).measurable).aestronglyMeasurable
  · have hu : w * (transposeReflection (r + 1) u).val * g = groupTranspose u.val * (w * g) := by
      rw [transposeReflection_eq, Whittaker.reflectedUnipotent_val, Subgroup.coe_inv]
      change w * (w * groupTranspose u.val * w) * g = _
      calc
        _ = (w * w) * (groupTranspose u.val * (w * g)) := by simp only [mul_assoc]
        _ = _ := by rw [weylLong_mul_self, one_mul]
    change ‖f (w * (transposeReflection (r + 1) u).val * g)‖ ≤ _
    rw [hu]
    exact norm_mul_le_sphericalMajorant hχ hcov (w * g) hC (groupTranspose u.val)

/-- Absolute convergence on the strict chamber of the complex upper-Borel standard module. -/
def ComplexJacquetOpenCellConvergenceStatement : Prop :=
  ∀ (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ),
    IsPhasePower χ e → IsStrictlyDominant e r →
    ∀ f ∈ principalSeries ℂ (r + 1) χ, ∀ g : Langlands.GeneralLinear (r + 1) ℂ,
      Integrable (fun u : upperUnipotent (r + 1) ℂ => f (weylLong (r + 1) ℂ * u.val * g))
        (entryHaar μ (r + 1))

theorem complexJacquetOpenCellConvergence : ComplexJacquetOpenCellConvergenceStatement := by
  intro r μ χ e hχ he f hf g
  exact integrable_openCell_of_borelCovariance μ hχ he hf.1.continuous hf.2 g

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberConvergence
