import Langlands.Global.RankinSelberg.ComplexLocalCompactAveraging
import Langlands.Global.RankinSelberg.ComplexLocalMatrixMajorant
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRegularity

/-! # Absolute integrability for the compact insertion -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Manifold ContDiff Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel

variable {r : ℕ}

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "H" => complexMatrixHeight

local instance compactInsertionSecondCountable : SecondCountableTopology G :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

/-- For a Whittaker coefficient, the compact averaging kernel is integrable at every
fixed left multiplier on a single right half-plane. -/
def ComplexLocalCompactInsertionIntegrabilityStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ] (ν : Measure K) [IsFiniteMeasure ν]
    (i : K →* K), Continuous i →
  ∀ (κ : K → ℂ), Continuous κ →
  ∀ (d : ComplexCharacterData) (Φ : 𝓢(Mat, ℂ))
    (ds : List ComplexCharacterData) (a : ℂˣ) (V : complexWhittakerModel r ds a),
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ x : G,
      let A := complexWeightedMatrixTest d.character Φ s
      Integrable (fun p : K × G => κ p.1 * A ((i p.1).val⁻¹ * p.2) * V.val (x * p.2))
        (ν.prod μ)

theorem complexLocalCompactInsertionIntegrability :
    ComplexLocalCompactInsertionIntegrabilityStatement (r := r) := by
  intro μ _ _ ν _ i hi κ hκ d Φ ds a V
  obtain ⟨C, M, hC, hV⟩ := complexWhittakerModel_moderateGrowth V.2
  refine ⟨(n : ℝ) + M - d.exponent.re, fun s hs x => ?_⟩
  let A := complexWeightedMatrixTest d.character Φ s
  let E (g : G) : ℝ := max 1 (H g)
  let ι := (unitaryCompact ℂ n).subtype.comp i
  have hι : Continuous ι := continuous_subtype_val.comp hi
  have hE : Continuous E := continuous_const.max continuous_complexMatrixHeight
  have hA : Continuous A :=
    ((Φ.continuous.comp Units.continuous_val).mul
      (Units.continuous_val.comp (d.character.continuous.comp continuous_complexDeterminant))).mul
      (continuous_complexDetPower s)
  have hVc := (contMDiff_of_mem_complexWhittakerModel V.2).continuous
  change Integrable (fun p : K × G => κ p.1 * A ((ι p.1)⁻¹ * p.2) * V.val (x * p.2)) _
  simp_rw [← map_inv]
  refine (integrable_compact_average_iff ι hι.measurable ν μ κ A
    (fun g => V.val (x * g))).mpr ?_
  let T (k : K) := C * E (x * ι k) ^ M * ‖κ k‖
  have hT : Continuous T :=
    (((hE.comp (continuous_const.mul hι)).pow M).const_mul C).mul hκ.norm
  let B (g : G) := E g ^ M * ‖A g‖
  have hB : Integrable B μ := by
    apply complexLocalMatrixMajorant n M μ d Φ s
    rw [Complex.add_re, Nat.cast_add, Nat.cast_one]
    linarith
  have hTi : Integrable T ν :=
    hT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace T)
  refine (hTi.mul_prod hB).mono'
    ((hA.comp continuous_snd).mul ((hκ.comp continuous_fst).mul
      (hVc.comp (continuous_const.mul ((hι.comp continuous_fst).mul continuous_snd))))).aestronglyMeasurable
    (ae_of_all _ ?_)
  rintro ⟨k, g⟩
  have hP : ‖V.val (x * (ι k * g))‖ ≤ C * (E (x * ι k) ^ M * E g ^ M) := by
    rw [← mul_assoc, ← mul_pow]
    exact (hV ((x * ι k) * g)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
        (max_complexMatrixHeight_mul_le _ _) _) hC)
  simp only [norm_mul]
  calc
    ‖A g‖ * (‖κ k‖ * ‖V.val (x * (ι k * g))‖) ≤
        ‖A g‖ * (‖κ k‖ * (C * (E (x * ι k) ^ M * E g ^ M))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (norm_nonneg _)) (norm_nonneg _)
    _ = T k * B g := by dsimp only [T, B]; ring

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
