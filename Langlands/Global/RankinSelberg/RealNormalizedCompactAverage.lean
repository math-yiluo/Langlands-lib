import Langlands.Global.RankinSelberg.RealCompactDualProbe
import Langlands.Global.RankinSelberg.RealExactCompactProjection
import Langlands.Global.RankinSelberg.RealModulusOpenCell
import Langlands.Global.RankinSelberg.RealOppositeDilation

/-!
# Normalized compact averages from opposite-cell contraction

Project a genuine right translate of a fixed standard vector with the
inverse-translation coefficient of the input. The compact pairing and
modulus integral identify it with an average on the opposite cell. The
same normalization scales the compatible exact Whittaker projection.
-/

noncomputable section

open MeasureTheory
open scoped Classical ENNReal Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealNormalizedCompactAverage

open Langlands.Archimedean (realPositionCharacter principalSeries principalSeriesCharacter unitaryCompact
  kFiniteVectors mem_kFiniteVectors_iff rightTranslation_mem_principalSeries matrixModel)
open Langlands.Archimedean.RealPrincipalSeriesDuality (haarK)
open Langlands.Archimedean.MaximalParabolicIntegration (modulusCharacter IsModulusCovariant)
open Langlands.Archimedean.JacquetLimit (principalSeriesCharacter_dual_mul)
open Langlands.Archimedean.PartialJacquet (norm_principalSeriesCharacter)
open Langlands.Archimedean.RealStrictCharacterLanglandsQuotient (isSignedPower)
open Langlands.LocalFactor.Archimedean (RealBlock)
open RealCompactDualProbe (dualSection realCompactDualProbe)
open RealModulusOpenCell (realEntryLebesgue groupTranspose realModulusOpenCell)
open RealOppositeDilation (contractionDiagonal contraction contractionDegree continuous_contraction
  map_contraction transpose_contraction)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "U" => fun n => unitaryCompact ℝ n
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ
local notation "Std" => Automorphic.realStandardKFinite

local instance realNormalizedAverageKMeasurable (j : ℕ) :
    MeasurableSpace (unitaryCompact ℝ j) := borel _
local instance realNormalizedAverageKBorel (j : ℕ) : BorelSpace (unitaryCompact ℝ j) := ⟨rfl⟩
local instance realNormalizedAverageNMeasurable (n : ℕ) : MeasurableSpace (N n) := borel _
local instance realNormalizedAverageNBorel (n : ℕ) : BorelSpace (N n) := ⟨rfl⟩

variable {n : ℕ}

/-- The diagonal entries of the contracting positive torus element. -/
def contractionArguments (n : ℕ) {ε : ℝ} (hε : 0 < ε) : Fin n → ℝˣ :=
  fun i => (Units.mk0 ε hε.ne') ^ i.val

theorem diagonalUnits_contractionArguments (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Langlands.GeneralLinear.Iwasawa.diagonalUnits (contractionArguments n hε) = contractionDiagonal n hε :=
  rfl

/-- The ordinary standard-module character on the contracting diagonal. -/
def contractionCharacter (n : ℕ) (ds : List RealBlock) {ε : ℝ} (hε : 0 < ε) : ℂ :=
  principalSeriesCharacter ℝ n (realPositionCharacter ds) (contractionArguments n hε)

theorem contractionCharacter_ne_zero (n : ℕ) (ds : List RealBlock) {ε : ℝ} (hε : 0 < ε) :
    contractionCharacter n ds hε ≠ 0 := by
  rw [← norm_ne_zero_iff, contractionCharacter, norm_principalSeriesCharacter (isSignedPower ds)]
  exact (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos
    (norm_pos_iff.mpr (contractionArguments n hε i).ne_zero) _).ne'

/-- The unweighted mass of a standard vector on the opposite cell. -/
def oppositeMass {ds : List RealBlock} (f₀ : Std n ds) : ℂ :=
  ∫ u : N n, f₀.val (groupTranspose u.val) ∂realEntryLebesgue n

/-- The compact chart constant, real Jacobian, and inducing character in the compact pairing. -/
def averageFactor (c : ℝ) (ds : List RealBlock) {ε : ℝ} (hε : 0 < ε) (n : ℕ) : ℂ :=
  (c : ℂ) * ((ε ^ contractionDegree n : ℝ) : ℂ) * contractionCharacter n ds hε

theorem averageFactor_ne_zero {c : ℝ} (hc : 0 < c) (ds : List RealBlock)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) : averageFactor c ds hε n ≠ 0 := by
  unfold averageFactor
  exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hε.ne'))) (contractionCharacter_ne_zero n ds hε)

/-- The reciprocal factors that give unit mass in the opposite-cell average. -/
def averageScale (c : ℝ) {ds : List RealBlock} (f₀ : Std n ds)
    {ε : ℝ} (hε : 0 < ε) : ℂ :=
  (oppositeMass f₀)⁻¹ * (averageFactor c ds hε n)⁻¹

/-- The integrand after contracting the domain of the dual probe on the opposite cell. -/
def contractedPair {ds : List RealBlock} (f f₀ : Std n ds) (x : K n)
    {ε : ℝ} (hε : 0 < ε) (u : N n) : ℂ :=
  f₀.val (groupTranspose u.val) * dualSection f x (groupTranspose (contraction n hε u).val)

private theorem translatedSection_contraction {ds : List RealBlock} (f₀ : Std n ds)
    {ε : ℝ} (hε : 0 < ε) (u : N n) :
    f₀.val (groupTranspose (contraction n hε u).val * contractionDiagonal n hε) =
      contractionCharacter n ds hε * f₀.val (groupTranspose u.val) := by
  rw [transpose_contraction, mul_assoc, inv_mul_cancel, mul_one, ← diagonalUnits_contractionArguments]
  simpa only [contractionCharacter, Subgroup.coe_one, mul_one] using
    f₀.2.1.1.2 (contractionArguments n hε) 1 (groupTranspose u.val)

private theorem dual_mul_translate_mem_modulus {ds : List RealBlock} (f f₀ : Std n ds)
    (x : K n) (g : G n) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (fun y => dualSection f x y * f₀.val (y * g)) ∧
      IsModulusCovariant (fun y => dualSection f x y * f₀.val (y * g)) := by
  have hf := RealCompactDualProbe.dualSection_mem f x
  have hf₀ := rightTranslation_mem_principalSeries _ f₀.2.1.1 g
  refine ⟨Langlands.Archimedean.contMDiff_of_contDiffOn
    ((Langlands.Archimedean.contDiffOn_unitsExtension hf.1).mul
      (Langlands.Archimedean.contDiffOn_unitsExtension hf₀.1)) (fun y => by
        simp only [Langlands.Archimedean.unitsExtension_val]; rfl), fun a u y => ?_⟩
  change dualSection f x _ * (Whittaker.rightTranslation ℂ (G n) g f₀.val) _ =
    _ * (dualSection f x y * (Whittaker.rightTranslation ℂ (G n) g f₀.val) y)
  rw [hf.2, hf₀.2, ← principalSeriesCharacter_dual_mul (isSignedPower ds)]
  ring

private theorem pair_after_contraction (c : ℝ)
    (hc : ∀ F : G n → ℂ, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ F → IsModulusCovariant F →
      Integrable (fun u : N n => F (groupTranspose u.val)) (realEntryLebesgue n) ∧
        (∫ k : U n, F k.val ∂haarK n) =
          (c : ℂ) * ∫ u : N n, F (groupTranspose u.val) ∂realEntryLebesgue n)
    {ds : List RealBlock} (f f₀ : Std n ds) (x : K n) {ε : ℝ} (hε : 0 < ε) :
    Integrable (contractedPair f f₀ x hε) (realEntryLebesgue n) ∧
    (∫ k : U n, f.val (k.val⁻¹ * Unitary.toUnits x) *
        f₀.val (k.val * contractionDiagonal n hε) ∂haarK n) =
      averageFactor c ds hε n * ∫ u : N n, contractedPair f f₀ x hε u ∂realEntryLebesgue n := by
  let ν := realEntryLebesgue n
  let a := contractionDiagonal n hε
  let F : G n → ℂ := fun y => dualSection f x y * f₀.val (y * a)
  let H : N n → ℂ := fun u => F (groupTranspose u.val)
  have hF := dual_mul_translate_mem_modulus f f₀ x a
  obtain ⟨hH, hint⟩ := hc F hF.1 hF.2
  have hcH : Continuous H := hF.1.continuous.comp
    (((Langlands.GeneralLinear.continuous_inverseTranspose n ℝ).comp continuous_inv).comp continuous_subtype_val)
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
    _ = ∫ k : U n, F k.val ∂haarK n := (realCompactDualProbe n ds f f₀ x a).2.2.symm
    _ = (c : ℂ) * ∫ u : N n, H u ∂ν := hint
    _ = (c : ℂ) * ((ε ^ contractionDegree n : ℝ) : ℂ) *
        (∫ u : N n, H (contraction n hε u) ∂ν) := by
      rw [he, mul_assoc, mul_inv_cancel_left₀ hj]
    _ = _ := by simp_rw [hv, integral_const_mul, averageFactor, mul_assoc, ν]

/-- The restriction of the input standard section to the inverse compact variable. -/
def inverseWeight {ds : List RealBlock} (f : Std n ds) : C(U n, ℂ) :=
  ⟨fun k => f.val k.val⁻¹, f.2.1.1.1.continuous.comp continuous_subtype_val.inv⟩

private theorem inverseWeight_finite {ds : List RealBlock} (f : Std n ds) :
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

private theorem integral_unitary_shift {ds : List RealBlock} (f f₀ : Std n ds)
    (x : K n) (g : G n) :
    (∫ k : U n, inverseWeight f k * f₀.val (Unitary.toUnits x * k.val * g) ∂haarK n) =
      ∫ k : U n, f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g) ∂haarK n := by
  let κ : U n := ⟨Unitary.toUnits x, x.2⟩
  conv_rhs => rw [← integral_mul_left_eq_self _ κ]
  apply integral_congr_ae (ae_of_all _ fun k => ?_)
  change f.val k.val⁻¹ * f₀.val (κ.val * k.val * g) =
    f.val ((κ * k : U n).val⁻¹ * κ.val) * f₀.val ((κ * k : U n).val * g)
  rw [Subgroup.coe_mul, mul_inv_rev, mul_assoc _ _ κ.val, inv_mul_cancel, mul_one]

/-- The normalized compact average compatible with an exact Whittaker intertwiner. Its compact
values are the normalized opposite-cell integrals of the contracted dual probes. -/
def RealNormalizedCompactAverageStatement : Prop :=
  ∀ r : ℕ, ∃ c : ℝ, 0 < c ∧
  ∀ (ds : List RealBlock) (a : ℝˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsRealWhittakerIntertwiner r ds a B →
  ∀ (f₀ : Std (r + 1) ds), oppositeMass f₀ ≠ 0 →
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ A : Std (r + 1) ds →ₗ[ℂ] Std (r + 1) ds,
    (∀ (f : Std (r + 1) ds) (x : K (r + 1)),
      Integrable (contractedPair f f₀ x hε) (realEntryLebesgue (r + 1)) ∧
      (A f).val (Unitary.toUnits x) = (oppositeMass f₀)⁻¹ *
        ∫ u : N (r + 1), contractedPair f f₀ x hε u ∂realEntryLebesgue (r + 1)) ∧
    (∀ f (y : G (r + 1)), (A f).val y = averageScale c f₀ hε *
      ∫ k : U (r + 1), inverseWeight f k * f₀.val (y * k.val * contractionDiagonal (r + 1) hε)
        ∂haarK (r + 1)) ∧
    ∀ f (y : G (r + 1)), B (A f) y = averageScale c f₀ hε *
      ∫ k : U (r + 1), inverseWeight f k * B f₀ (y * k.val * contractionDiagonal (r + 1) hε)
        ∂haarK (r + 1)

theorem realNormalizedCompactAverage : RealNormalizedCompactAverageStatement := by
  intro r
  obtain ⟨c, hc, hchart⟩ := realModulusOpenCell (r + 1)
  refine ⟨c, hc, fun ds a B hB f₀ _ ε hε => ?_⟩
  let d := contractionDiagonal (r + 1) hε
  let S := Std (r + 1) ds
  choose P hP hBP using fun f : S => realExactCompactProjection r ds a (haarK (r + 1))
    inferInstance (inverseWeight f) (inverseWeight_finite f) B hB f₀ d
  have hIntegrable (f : S) (y : G (r + 1)) : Integrable
      (fun k : U (r + 1) => inverseWeight f k * f₀.val (y * k.val * d)) (haarK (r + 1)) :=
    ((inverseWeight f).continuous.mul (f₀.2.1.1.1.continuous.comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
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

end Langlands.Global.RankinSelbergGlobal.RealNormalizedCompactAverage
