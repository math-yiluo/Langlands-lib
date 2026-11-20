import Langlands.Global.RankinSelberg.ComplexGodementCompact
import Langlands.Global.RankinSelberg.ComplexGodementJacquetComparison
import Langlands.Global.RankinSelberg.ComplexJacquetChamberConvergence
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient

/-! # Absolute convergence of the joint complex Godement Jacquet integral -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementChamberComparison

open Langlands.Archimedean (complexStandardModule complexPositionCharacter principalSeries)
open Langlands.Archimedean.ComplexGramFormula (complexPositionExponent)
open Langlands.Archimedean.ComplexPartialJacquet (IsStrictlyDominant exists_bound_unitaryCompact)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC det_upperUnipotent)
open Langlands.Archimedean.ComplexStrictLanglandsQuotient (isPhasePower)
open Langlands.GeneralLinear (determinant weylLong)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open Langlands.Shahidi (unipotentProduct unipotentProductMeasure
  continuous_unipotentProduct integrable_unipotentProductMeasure_iff)
open ComplexGodement
open ComplexGodementJacquetComparison (jointKernel openCellIntegral openCellIntegral_godementSection)
open ComplexGodementColumnChange (iteratedKernel)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite unipotentProductMeasure_entryHaar)
open ComplexJacquetChamberConvergence (radialChar sphericalMajorant sphericalMajorant_mem
  sphericalMajorant_ofReal_norm norm_mul_le_sphericalMajorant integrable_openCell_of_borelCovariance)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

private def absoluteCharacterHom (d : ComplexCharacterData) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 (‖(d.character z : ℂ)‖ : ℂ)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (d.character z).ne_zero))
  map_one' := Units.ext (by simp)
  map_mul' z y := Units.ext (by simp [Complex.ofReal_mul])

private theorem norm_character (d : ComplexCharacterData) (z : ℂˣ) :
    ‖(d.character z : ℂ)‖ = ‖(z : ℂ)‖ ^ (2 * d.exponent.re) := by
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hphase : ‖(z : ℂ) / (‖(z : ℂ)‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hz.le, div_self hz.ne']
  rw [d.character_eq, norm_mul, Complex.norm_zpow, hphase, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hz]
  simp [Complex.mul_re]

/-- Take the absolute value of a complex inducing character, expressed as a positive
complex character with its real exponent. -/
def absoluteCharacter (d : ComplexCharacterData) : ComplexCharacterData where
  character := {
    toMonoidHom := absoluteCharacterHom d
    continuous_toFun := by
      apply Units.continuous_iff.mpr
      have hc : Continuous fun z : ℂˣ => (absoluteCharacterHom d z : ℂ) :=
        Complex.continuous_ofReal.comp (Units.continuous_val.comp d.character.continuous).norm
      refine ⟨hc, ?_⟩
      change Continuous (fun z : ℂˣ => ((absoluteCharacterHom d z)⁻¹ : ℂˣ).val)
      simpa only [Function.comp_def, map_inv] using hc.comp continuous_inv }
  weight := 0
  exponent := d.exponent.re
  character_eq z := by
    change (‖(d.character z : ℂ)‖ : ℂ) =
      ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (0 : ℤ) * (‖(z : ℂ)‖ : ℂ) ^ (2 * (d.exponent.re : ℂ))
    rw [zpow_zero, one_mul, ← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_mul,
      ← Complex.ofReal_cpow (norm_nonneg _), norm_character]

private theorem characterWeight_absolute (d : ComplexCharacterData) (s : ℝ) (z : ℂˣ) :
    characterWeight (absoluteCharacter d) (s : ℂ) z = (‖characterWeight d (s : ℂ) z‖ : ℂ) := by
  change (‖(d.character z : ℂ)‖ : ℂ) * (normSqC (z : ℂ)) ^ (s : ℂ) =
    (‖(d.character z : ℂ) * (normSqC (z : ℂ)) ^ (s : ℂ)‖ : ℂ)
  rw [norm_mul, Complex.ofReal_mul, normSqC, ← Complex.ofReal_cpow (sq_nonneg _),
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _)]

private theorem absoluteExponent (ds : List ComplexCharacterData) (i : ℕ) :
    complexPositionExponent (ds.map absoluteCharacter) i = ((complexPositionExponent ds i).re : ℂ) := by
  induction ds generalizing i with
  | nil => simp [complexPositionExponent]
  | cons d ds ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem absolutePosition (ds : List ComplexCharacterData) :
    complexPositionCharacter (ds.map absoluteCharacter) = radialChar (fun i => (complexPositionExponent ds i).re) := by
  funext i z
  induction ds generalizing i with
  | nil => simp [complexPositionCharacter, radialChar, complexPositionExponent]
  | cons d ds ih =>
    cases i with
    | zero =>
      change (‖(d.character z : ℂ)‖ : ℂ) = ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (d.exponent.re : ℂ)
      rw [norm_character, ← Complex.ofReal_cpow (sq_nonneg _), ← Real.rpow_natCast,
        ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    | succ i => exact ih i

private theorem mul_eq_ofReal_norm {x y : ℂ} (hx : x = (‖x‖ : ℂ)) (hy : y = (‖y‖ : ℂ)) :
    x * y = (‖x * y‖ : ℂ) := by
  rw [norm_mul, Complex.ofReal_mul, ← hx, ← hy]

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "U" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Col" => Fin (r + 1) → ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "w'" => weylLong (r + 1 + 1) ℂ

private theorem det_unipotent {n : ℕ} (u : GeneralLinear.upperUnipotent n ℂ) : determinant u.val = 1 :=
  Units.ext (det_upperUnipotent u)

/-- The absolute joint integrability required to compare the Godement section with (7.6)
for compactly supported tests on the full-row-rank locus in the strict chamber. -/
theorem integrable_jointKernel_of_chamber
    (ν : Measure G) [SFinite ν] [ν.IsMulRightInvariant] [IsLocallyFiniteMeasure ν]
    (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (he : IsStrictlyDominant (complexPositionExponent (d :: ds)) (r + 1)) (a : ℂˣ)
    {Φ : Rect → ℂ} (hΦ : Continuous Φ) (hcompact : HasCompactSupport Φ)
    (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (r + 1) ds) (g : G') :
    Integrable (jointKernel d a Φ f g) (((entryHaar μ (r + 1)).prod (rowMeasure μ (r + 1))).prod ν) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  have : SigmaFinite (entryHaar μ (r + 1)) := entryHaar_sigmaFinite μ (r + 1)
  let dn := entryHaar μ (r + 1)
  let dp := dn.prod (rowMeasure μ (r + 1))
  let d₀ := absoluteCharacter d
  let ds₀ := ds.map absoluteCharacter
  let t : ℕ → ℝ := fun i => (complexPositionExponent ds i).re
  let F := sphericalMajorant (r + 1) t
  let P : Rect → ℂ := fun X => (‖Φ X‖ : ℂ)
  have hF : F ∈ complexStandardModule (r + 1) ds₀ := by
    change F ∈ principalSeries ℂ (r + 1) (complexPositionCharacter ds₀)
    rw [absolutePosition ds]
    exact (sphericalMajorant_mem (r + 1) t).1
  have hdom : IsStrictlyDominant (complexPositionExponent (d₀ :: ds₀)) (r + 1) := by
    intro i hi
    change (complexPositionExponent ((d :: ds).map absoluteCharacter) (i + 1)).re <
      (complexPositionExponent ((d :: ds).map absoluteCharacter) i).re
    simpa only [absoluteExponent, Complex.ofReal_re] using he i hi
  have hP : Continuous P := Complex.continuous_ofReal.comp hΦ.norm
  have hsupp : Function.support P = Function.support Φ := by
    ext X
    simp [P, Function.mem_support]
  have hPc : HasCompactSupport P := by simpa only [HasCompactSupport, tsupport, hsupp] using hcompact
  have hPr : ∀ X ∈ tsupport P, HasFullRowRank X := by simpa only [tsupport, hsupp] using hfull
  let b : U × Col → G' := fun p => w' * (unipotentProduct p).val * g
  let K : (U × Col) × G → ℂ := fun p => godementSectionIntegrand d₀ P F (b p.1) p.2
  let S := godementSection ν d₀ P F
  have hS : Continuous S := continuous_godementSection_of_hasCompactSupport ν d₀ hP hPc hPr hF.1.continuous
  have hSb := godementSection_covariant ν d₀ ds₀ P hF
  have hbig := integrable_openCell_of_borelCovariance μ (isPhasePower (d₀ :: ds₀)) hdom hS hSb g
  have hInner : Integrable (fun p => S (b p)) dp := by
    apply (integrable_unipotentProductMeasure_iff dn (rowMeasure μ (r + 1))
      (fun u => S (w' * u.val * g))).mp
    rwa [unipotentProductMeasure_entryHaar μ (r + 1)]
  let s : ℂ := (((r + 1 : ℕ) : ℂ) / 2)
  let u : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2)
  have hreal : u = ((((r + 1 : ℕ) + 1 : ℝ) / 2 : ℝ) : ℂ) := by simp [u]
  have hweight (h : G) : characterWeight d₀ u (determinant h) =
      (‖characterWeight d u (determinant h)‖ : ℂ) := by
    rw [hreal]
    exact characterWeight_absolute d _ _
  have hKpos (p : (U × Col) × G) : K p = (‖K p‖ : ℂ) := by
    have hPpos (X : Rect) : P X = (‖P X‖ : ℂ) := by
      dsimp only [P]
      rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    unfold K godementSectionIntegrand
    refine mul_eq_ofReal_norm (mul_eq_ofReal_norm (hPpos _) (sphericalMajorant_ofReal_norm t _)) ?_
    change characterWeight d₀ u (determinant p.2) = (‖characterWeight d₀ u (determinant p.2)‖ : ℂ)
    rw [hweight, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  let A := characterWeight d₀ s (determinant (w' * g))
  have hA : A ≠ 0 := by
    unfold A
    change ((d₀.character (determinant (w' * g)) : ℂ) *
      (normSqC (determinant (w' * g) : ℂ)) ^ s) ≠ 0
    exact mul_ne_zero (d₀.character _).ne_zero (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Langlands.Archimedean.ComplexMaximalParabolicIntegration.normSqC_ne_zero
        (determinant (w' * g)).ne_zero)))
  have hpref (p : U × Col) : characterWeight d₀ s (determinant (b p)) = A := by
    dsimp only [A, b]
    rw [map_mul determinant, map_mul determinant, det_unipotent, mul_one, map_mul determinant]
  have hInnerNorm (p : U × Col) : ‖S (b p)‖ = ‖A‖ * ∫ h, ‖K (p, h)‖ ∂ν := by
    have hfiber : (∫ h, K (p, h) ∂ν) = ((∫ h, ‖K (p, h)‖ ∂ν : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (ae_of_all _ fun h => hKpos (p, h))
    change ‖characterWeight d₀ s (determinant (b p)) * (∫ h, K (p, h) ∂ν)‖ = _
    rw [hpref, norm_mul, hfiber, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hb : Continuous b := (continuous_const.mul
    (continuous_subtype_val.comp continuous_unipotentProduct)).mul continuous_const
  have hK : Integrable K (dp.prod ν) := by
    refine (integrable_prod_iff ((continuous_godementSectionIntegrand d₀ hP hF.1.continuous).comp
      ((hb.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact ae_of_all _ fun p => integrable_godementSectionIntegrand ν d₀ hP hPc hPr hF.1.continuous (b p)
    · refine (hInner.norm.const_mul ‖A‖⁻¹).congr (ae_of_all _ fun p => ?_)
      change ‖A‖⁻¹ * ‖S (b p)‖ = ∫ h, ‖K (p, h)‖ ∂ν
      rw [hInnerNorm, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA), one_mul]
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hf.1.continuous
  have hbound (h : G) : ‖f h‖ ≤ C * ‖F h‖ := by
    simpa only [mul_one] using norm_mul_le_sphericalMajorant (isPhasePower ds) hf.2 1
      (fun k hk => by simpa only [mul_one] using hC k hk) h
  have hJoint : Continuous (jointKernel d a Φ f g) := by
    apply ((continuous_godementSectionIntegrand d hΦ hf.1.continuous).comp
      ((hb.comp continuous_fst).prodMk continuous_snd)).mul
    unfold complexWhittakerCharacter
    apply (complexScaledCharacter a).continuous_complex.comp
    exact continuous_finsetSum _ fun i _ => (GeneralLinear.entry i.castSucc i.succ).continuous.comp
      ((continuous_subtype_val.comp continuous_unipotentProduct).comp continuous_fst)
  refine (hK.norm.const_mul C).mono' hJoint.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  unfold jointKernel godementSectionIntegrand complexWhittakerCharacter
  simp only [norm_mul, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex, mul_one]
  calc
    _ ≤ ‖Φ (p.2.val * trailingRows (b p.1).val)‖ * (C * ‖F p.2⁻¹‖) *
        ‖characterWeight d u (determinant p.2)‖ := by
      gcongr
      exact hbound p.2⁻¹
    _ = _ := by
      change _ = C * ‖P (p.2.val * trailingRows (b p.1).val) * F p.2⁻¹ *
        characterWeight d₀ u (determinant p.2)‖
      rw [hweight]
      simp only [P, norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      ring

variable (r) in
/-- Formula (7.6) for a compact full-row-rank test in the strict upper-Borel chamber. -/
def ComplexGodementChamberComparisonStatement : Prop :=
  ∀ (ν : Measure G) [SFinite ν] [ν.IsMulRightInvariant] [IsLocallyFiniteMeasure ν]
    (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData) (ds : List ComplexCharacterData),
    IsStrictlyDominant (complexPositionExponent (d :: ds)) (r + 1) →
    ∀ (a : ℂˣ) (Φ : Rect → ℂ), Continuous Φ → HasCompactSupport Φ →
    (∀ X ∈ tsupport Φ, HasFullRowRank X) →
    ∀ f ∈ complexStandardModule (r + 1) ds, ∀ g : G',
      openCellIntegral a (entryHaar μ (r + 1 + 1)) (godementSection ν d Φ f) g =
        (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
          characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant g) *
            ∫ h, iteratedKernel (complexScaledCharacter a) μ d (fun X => Φ (X * g.val))
              (openCellIntegral a (entryHaar μ (r + 1)) f) (((r + 1 : ℕ) + 1 : ℂ) / 2) h ∂ν

theorem complexGodementChamberComparison : ComplexGodementChamberComparisonStatement r := by
  intro ν hν hr hl μ d ds he a Φ hΦ hcompact hfull f hf g
  have : SigmaFinite (entryHaar μ (r + 1)) := entryHaar_sigmaFinite μ (r + 1)
  rw [← unipotentProductMeasure_entryHaar μ (r + 1)]
  exact openCellIntegral_godementSection ν (entryHaar μ (r + 1)) μ d a Φ f g
    (integrable_jointKernel_of_chamber ν μ d ds he a hΦ hcompact hfull hf g)

end Langlands.Global.RankinSelbergGlobal.ComplexGodementChamberComparison
