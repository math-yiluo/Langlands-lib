import Langlands.Global.RankinSelberg.ComplexCompactDualProbe
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerGrowth
import Langlands.Global.RankinSelberg.ComplexModulusOpenCell
import Langlands.Global.RankinSelberg.ComplexOppositeDilation

/-!
# Normalized compact averages from opposite-cell contraction

Project a genuine right translate of a fixed standard vector with the
inverse-translation coefficient of the input. The compact pairing and
modulus integral identify it with an average on the opposite cell. The
same normalization scales the compatible exact Whittaker projection.
-/

noncomputable section

open MeasureTheory
open scoped Classical ENNReal Matrix.Norms.Operator Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexNormalizedCompactAverage

open Langlands.Archimedean (complexPositionCharacter principalSeries principalSeriesCharacter unitaryCompact kFiniteVectors
  mem_kFiniteVectors_iff rightTranslation_mem_principalSeries)
open Langlands.Archimedean.ComplexDuality (unitaryHaar integrable_unitaryHaar)
open Langlands.Archimedean.ComplexGramFormula (complexPositionExponent)
open Langlands.Archimedean.ComplexKIntegralInvariance (modulusCharacter)
open Langlands.Archimedean.ComplexJacquetLimit (contMDiff_mul_fun principalSeriesCharacter_dual_mul)
open Langlands.Archimedean.ComplexPartialJacquet (norm_principalSeriesCharacter)
open Langlands.Archimedean.ComplexStrictLanglandsQuotient (isPhasePower)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactDualProbe (dualSection complexCompactDualProbe)
open ComplexLocalWhittakerGrowth (complexWhittakerCompactProjection)
open ComplexModulusOpenCell (complexEntryLebesgue groupTranspose complexModulusOpenCell)
open ComplexOppositeDilation (contractionDiagonal contraction contractionDegree continuous_contraction
  map_contraction transpose_contraction)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "U" => fun n => unitaryCompact ℂ n
local notation "N" => fun n => GeneralLinear.upperUnipotent n ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Std" => Automorphic.complexStandardKFinite

local instance normalizedAverageNMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance normalizedAverageNBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

variable {n : ℕ}

/-- The diagonal entries of the contracting positive torus element. -/
def contractionArguments (n : ℕ) {ε : ℝ} (hε : 0 < ε) : Fin n → ℂˣ :=
  fun i => (Units.mk0 (ε : ℂ) (Complex.ofReal_ne_zero.mpr hε.ne')) ^ i.val

theorem diagonalUnits_contractionArguments (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    GeneralLinear.Iwasawa.diagonalUnits (contractionArguments n hε) = contractionDiagonal n hε := rfl

/-- The ordinary standard-module character on the contracting diagonal. -/
def contractionCharacter (n : ℕ) (ds : List ComplexCharacterData) {ε : ℝ} (hε : 0 < ε) : ℂ :=
  principalSeriesCharacter ℂ n (complexPositionCharacter ds) (contractionArguments n hε)

theorem contractionCharacter_ne_zero (n : ℕ) (ds : List ComplexCharacterData) {ε : ℝ} (hε : 0 < ε) :
    contractionCharacter n ds hε ≠ 0 := by
  rw [← norm_ne_zero_iff, contractionCharacter, norm_principalSeriesCharacter (isPhasePower ds)]
  exact (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos
    (norm_pos_iff.mpr (contractionArguments n hε i).ne_zero) _).ne'

/-- The unweighted mass of a standard vector on the opposite cell. -/
def oppositeMass {ds : List ComplexCharacterData} (f₀ : Std n ds) : ℂ :=
  ∫ u : N n, f₀.val (groupTranspose u.val) ∂complexEntryLebesgue n

/-- The compact chart constant, real Jacobian, and inducing character in the compact pairing. -/
def averageFactor (c : ℝ) (ds : List ComplexCharacterData) {ε : ℝ} (hε : 0 < ε) (n : ℕ) : ℂ :=
  (c : ℂ) * ((ε ^ contractionDegree n : ℝ) : ℂ) * contractionCharacter n ds hε

theorem averageFactor_ne_zero {c : ℝ} (hc : 0 < c) (ds : List ComplexCharacterData)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) : averageFactor c ds hε n ≠ 0 := by
  unfold averageFactor
  exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hε.ne'))) (contractionCharacter_ne_zero n ds hε)

/-- The reciprocal factors that give unit mass in the opposite-cell average. -/
def averageScale (c : ℝ) {ds : List ComplexCharacterData} (f₀ : Std n ds)
    {ε : ℝ} (hε : 0 < ε) : ℂ :=
  (oppositeMass f₀)⁻¹ * (averageFactor c ds hε n)⁻¹

/-- The integrand after contracting the domain of the dual probe on the opposite cell. -/
def contractedPair {ds : List ComplexCharacterData} (f f₀ : Std n ds) (x : K n)
    {ε : ℝ} (hε : 0 < ε) (u : N n) : ℂ :=
  f₀.val (groupTranspose u.val) * dualSection f x (groupTranspose (contraction n hε u).val)

private theorem translatedSection_contraction {ds : List ComplexCharacterData} (f₀ : Std n ds)
    {ε : ℝ} (hε : 0 < ε) (u : N n) :
    f₀.val (groupTranspose (contraction n hε u).val * contractionDiagonal n hε) =
      contractionCharacter n ds hε * f₀.val (groupTranspose u.val) := by
  rw [transpose_contraction, mul_assoc, inv_mul_cancel, mul_one, ← diagonalUnits_contractionArguments]
  simpa only [contractionCharacter, Subgroup.coe_one, mul_one] using
    f₀.2.1.2 (contractionArguments n hε) 1 (groupTranspose u.val)

private theorem dual_mul_translate_mem_modulus {ds : List ComplexCharacterData} (f f₀ : Std n ds)
    (x : K n) (g : G n) :
    (fun y => dualSection f x y * f₀.val (y * g)) ∈ principalSeries ℂ n (modulusCharacter n) := by
  have hf := ComplexCompactDualProbe.dualSection_mem f x
  have hf₀ := rightTranslation_mem_principalSeries _ f₀.2.1 g
  refine ⟨contMDiff_mul_fun hf.1 hf₀.1, fun a u y => ?_⟩
  change dualSection f x _ * (Whittaker.rightTranslation ℂ (G n) g f₀.val) _ =
    _ * (dualSection f x y * (Whittaker.rightTranslation ℂ (G n) g f₀.val) y)
  rw [hf.2, hf₀.2, ← principalSeriesCharacter_dual_mul (isPhasePower ds)]
  ring

private theorem pair_after_contraction (c : ℝ)
    (hc : ∀ F : G n → ℂ, F ∈ principalSeries ℂ n (modulusCharacter n) →
      Integrable (fun u : N n => F (groupTranspose u.val)) (complexEntryLebesgue n) ∧
        (∫ k : U n, F k.val ∂unitaryHaar n) =
          (c : ℂ) * ∫ u : N n, F (groupTranspose u.val) ∂complexEntryLebesgue n)
    {ds : List ComplexCharacterData} (f f₀ : Std n ds) (x : K n) {ε : ℝ} (hε : 0 < ε) :
    Integrable (contractedPair f f₀ x hε) (complexEntryLebesgue n) ∧
    (∫ k : U n, f.val (k.val⁻¹ * Unitary.toUnits x) *
        f₀.val (k.val * contractionDiagonal n hε) ∂unitaryHaar n) =
      averageFactor c ds hε n * ∫ u : N n, contractedPair f f₀ x hε u ∂complexEntryLebesgue n := by
  let ν := complexEntryLebesgue n
  let a := contractionDiagonal n hε
  let F : G n → ℂ := fun y => dualSection f x y * f₀.val (y * a)
  let H : N n → ℂ := fun u => F (groupTranspose u.val)
  have hF : F ∈ principalSeries ℂ n (modulusCharacter n) := dual_mul_translate_mem_modulus f f₀ x a
  obtain ⟨hH, hint⟩ := hc F hF
  have hcH : Continuous H := hF.1.continuous.comp
    (((GeneralLinear.continuous_inverseTranspose n ℂ).comp continuous_inv).comp continuous_subtype_val)
  have hδ := (continuous_contraction n hε).measurable
  have hmap := map_contraction n hε
  have hH' : Integrable H (ν.map (contraction n hε)) := by
    rw [hmap]
    exact hH.smul_measure ENNReal.ofReal_ne_top
  have hComp : Integrable (fun u => H (contraction n hε u)) ν :=
    (integrable_map_measure hcH.aestronglyMeasurable hδ.aemeasurable).mp hH'
  have hv (u : N n) : H (contraction n hε u) = contractionCharacter n ds hε * contractedPair f f₀ x hε u := by
    dsimp only [H, F, a, contractedPair]
    rw [translatedSection_contraction]
    ring
  have hPair : Integrable (contractedPair f f₀ x hε) ν := by
    refine (hComp.const_mul (contractionCharacter n ds hε)⁻¹).congr (ae_of_all _ fun u => ?_)
    change (contractionCharacter n ds hε)⁻¹ * H (contraction n hε u) = contractedPair f f₀ x hε u
    rw [hv, inv_mul_cancel_left₀ (contractionCharacter_ne_zero n ds hε)]
  have he : (∫ u : N n, H (contraction n hε u) ∂ν) =
      ((ε ^ contractionDegree n : ℝ) : ℂ)⁻¹ * ∫ u : N n, H u ∂ν := by
    rw [← integral_map hδ.aemeasurable hcH.aestronglyMeasurable, hmap, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity), Complex.real_smul, Complex.ofReal_inv]
  have hj : ((ε ^ contractionDegree n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hε.ne')
  refine ⟨hPair, ?_⟩
  calc
    _ = ∫ k : U n, F k.val ∂unitaryHaar n := (complexCompactDualProbe n ds f f₀ x a).2.2.symm
    _ = (c : ℂ) * ∫ u : N n, H u ∂ν := hint
    _ = (c : ℂ) * ((ε ^ contractionDegree n : ℝ) : ℂ) *
        (∫ u : N n, H (contraction n hε u) ∂ν) := by
      rw [he, mul_assoc, mul_inv_cancel_left₀ hj]
    _ = _ := by simp_rw [hv, integral_const_mul, averageFactor, mul_assoc, ν]

/-- The restriction of the input standard section to the inverse compact variable. -/
def inverseWeight {ds : List ComplexCharacterData} (f : Std n ds) : C(U n, ℂ) :=
  ⟨fun k => f.val k.val⁻¹, f.2.1.1.continuous.comp continuous_subtype_val.inv⟩

private theorem inverseWeight_finite {ds : List ComplexCharacterData} (f : Std n ds) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : U n => fun k => inverseWeight f (h⁻¹ * k))) := by
  have hf : f.val ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (G n)) (U n) := f.2.2
  rw [mem_kFiniteVectors_iff] at hf
  let V := Submodule.span ℂ (Set.range fun h : U n => Whittaker.rightTranslation ℂ (G n) h.val f.val)
  let : FiniteDimensional ℂ V := hf
  let P : (G n → ℂ) →ₗ[ℂ] (U n → ℂ) := LinearMap.funLeft ℂ ℂ (fun k => k.val⁻¹)
  apply Submodule.finiteDimensional_of_le (S₂ := V.map P)
  apply Submodule.span_le.mpr
  rintro _ ⟨h, rfl⟩
  refine ⟨_, Submodule.subset_span ⟨h, rfl⟩, ?_⟩
  funext k
  change f.val (k.val⁻¹ * h.val) = f.val ((h⁻¹ * k : U n).val⁻¹)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]

private theorem integral_unitary_shift {ds : List ComplexCharacterData} (f f₀ : Std n ds)
    (x : K n) (g : G n) :
    (∫ k : U n, inverseWeight f k * f₀.val (Unitary.toUnits x * k.val * g) ∂unitaryHaar n) =
      ∫ k : U n, f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g) ∂unitaryHaar n := by
  let κ : U n := ⟨Unitary.toUnits x, x.2⟩
  conv_rhs => rw [← integral_mul_left_eq_self _ κ]
  apply integral_congr_ae (ae_of_all _ fun k => ?_)
  change f.val k.val⁻¹ * f₀.val (κ.val * k.val * g) =
    f.val ((κ * k : U n).val⁻¹ * κ.val) * f₀.val ((κ * k : U n).val * g)
  rw [Subgroup.coe_mul, mul_inv_rev, mul_assoc _ _ κ.val, inv_mul_cancel, mul_one]

/-- The normalized compact average compatible with an exact Whittaker intertwiner. Its compact
values are the normalized opposite-cell integrals of the contracted dual probes. -/
def ComplexNormalizedCompactAverageStatement : Prop :=
  ∀ r : ℕ, ∃ c : ℝ, 0 < c ∧
  ∀ (ds : List ComplexCharacterData) (a : ℂˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∀ (f₀ : Std (r + 1) ds), oppositeMass f₀ ≠ 0 →
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ A : Std (r + 1) ds →ₗ[ℂ] Std (r + 1) ds,
    (∀ (f : Std (r + 1) ds) (x : K (r + 1)),
      Integrable (contractedPair f f₀ x hε) (complexEntryLebesgue (r + 1)) ∧
      (A f).val (Unitary.toUnits x) = (oppositeMass f₀)⁻¹ *
        ∫ u : N (r + 1), contractedPair f f₀ x hε u ∂complexEntryLebesgue (r + 1)) ∧
    (∀ f (y : G (r + 1)), (A f).val y = averageScale c f₀ hε *
      ∫ k : U (r + 1), inverseWeight f k * f₀.val (y * k.val * contractionDiagonal (r + 1) hε)
        ∂unitaryHaar (r + 1)) ∧
    ∀ f (y : G (r + 1)), B (A f) y = averageScale c f₀ hε *
      ∫ k : U (r + 1), inverseWeight f k * B f₀ (y * k.val * contractionDiagonal (r + 1) hε)
        ∂unitaryHaar (r + 1)

theorem complexNormalizedCompactAverage : ComplexNormalizedCompactAverageStatement := by
  intro r
  obtain ⟨c, hc, hchart⟩ := complexModulusOpenCell (r + 1)
  refine ⟨c, hc, fun ds a B hB f₀ _ ε hε => ?_⟩
  let d := contractionDiagonal (r + 1) hε
  let S := Std (r + 1) ds
  choose P hP hBP using fun f : S => complexWhittakerCompactProjection (r := r) ds a (unitaryHaar (r + 1))
    inferInstance (inverseWeight f) (inverseWeight_finite f) B hB f₀ d
  have hIntegrable (f : S) (y : G (r + 1)) : Integrable
      (fun k : U (r + 1) => inverseWeight f k * f₀.val (y * k.val * d)) (unitaryHaar (r + 1)) :=
    integrable_unitaryHaar ((inverseWeight f).continuous.mul (f₀.2.1.1.continuous.comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)))
  let Q : S →ₗ[ℂ] S :=
    { toFun := P
      map_add' := fun f f' => by
        apply Subtype.ext
        funext y
        change (P (f + f')).val y = (P f).val y + (P f').val y
        rw [hP, hP, hP]
        simp only [inverseWeight, ContinuousMap.coe_mk, Submodule.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hIntegrable f y) (hIntegrable f' y)
      map_smul' := fun z f => by
        apply Subtype.ext
        funext y
        change (P (z • f)).val y = z * (P f).val y
        rw [hP, hP]
        simp only [inverseWeight, ContinuousMap.coe_mk, Submodule.coe_smul, Pi.smul_apply,
          smul_eq_mul, mul_assoc]
        exact integral_const_mul z _ }
  let scale := averageScale c f₀ hε
  let A : S →ₗ[ℂ] S := scale • Q
  have hA (f : S) (y : G (r + 1)) : (A f).val y = scale * (P f).val y := rfl
  refine ⟨A, fun f x => ?_, fun f y => (hA f y).trans (congrArg (scale * ·) (hP f y)), ?_⟩
  · obtain ⟨hi, hp⟩ := pair_after_contraction c hchart f f₀ x hε
    refine ⟨hi, ?_⟩
    rw [hA, hP, integral_unitary_shift, hp]
    simp only [scale, averageScale, mul_assoc, inv_mul_cancel_left₀ (averageFactor_ne_zero hc ds hε (r + 1))]
  · intro f y
    change B (scale • P f) y = _
    rw [map_smul, Pi.smul_apply, smul_eq_mul, hBP]

end Langlands.Global.RankinSelbergGlobal.ComplexNormalizedCompactAverage
