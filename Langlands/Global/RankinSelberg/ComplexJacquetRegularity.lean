import Langlands.Global.RankinSelberg.ComplexGodementCompactSpanning
import Langlands.Global.RankinSelberg.ComplexGodementContinuedSmooth
import Langlands.Global.RankinSelberg.ComplexJacquetGeneratorEvaluation

/-! # Group regularity and moderate growth of the canonical complex Jacquet evaluation -/

noncomputable section
open MeasureTheory Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (matrixModel characterOfParams)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ComplexPlaceAnalytic (complexMatrixHeight_inv two_le_complexMatrixHeight norm_entry_le_complexMatrixHeight)
open ComplexCompactProfileFamily (characterList standardSection standardSection_mem differentiable_standardSection
  standardSection_compactRestriction compactRestriction compactRestriction_isCompactProfile)
open ComplexGodement (compactGodementSections complexGodementCompactSpanning godementSection
  addedCharacter retainedCharacters smallerWeights smallerExponents smallerSection SmallerProfile characterList_cons)
open ComplexGodementWhittaker (augmentedPoint augmentedPoint_castSucc augmentedPoint_last inverse_log_length_le)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexGodementGeneratorFamily (generatorFamily)
open ComplexGodementContinuedSmooth (contMDiff_continuedValue)
open ComplexLocalIwasawa (alpha)
open RealConvergenceAnalysis (rootPos)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "P'" => Fin (r + 1 + 1) → ℂ
local notation "L'" => Fin (r + 1 + 1) → ℤ
local notation "Std'[" l "," p "]" => Automorphic.complexStandardKFinite (r + 1 + 1) (characterList l p)

open scoped Matrix.Norms.Elementwise in
private theorem norm_augmentedPoint_le_height (g : G) : ‖augmentedPoint g‖ ≤ complexMatrixHeight g := by
  have hn : 0 < r + 1 := Nat.succ_pos _
  apply (Matrix.norm_le_iff (zero_le_two.trans (two_le_complexMatrixHeight hn g))).mpr
  intro i j
  induction j using Fin.lastCases with
  | cast j =>
    rw [augmentedPoint_castSucc]
    exact norm_entry_le_complexMatrixHeight hn g i j
  | last =>
    rw [augmentedPoint_last, ← complexMatrixHeight_inv g]
    exact norm_entry_le_complexMatrixHeight hn g⁻¹ _ _

open scoped Matrix.Norms.Elementwise in
/-- The uniform logarithmic gauge implies polynomial growth in the exact Library height. -/
theorem exists_height_bound_of_uniformGauge {P : Type*} {S : Set P} {W : P → G → ℂ}
    (hW : HasUniformSimpleRootBound S W) {p : P} (hp : p ∈ S) :
    ∃ (C : ℝ) (M : ℕ), ∀ g, ‖W p g‖ ≤ C * complexMatrixHeight g ^ M := by
  obtain ⟨N, hN⟩ := hW
  let M := N * (r + 1)
  obtain ⟨C, hC, hb⟩ := hN M
  let b : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  refine ⟨C * b ^ M, M, fun g => ?_⟩
  let D : ℝ := ((r + 1 : ℕ) : ℝ) * (1 + ‖augmentedPoint g⁻¹‖)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDle : D ≤ b * complexMatrixHeight g := by
    have haug := norm_augmentedPoint_le_height g⁻¹
    rw [complexMatrixHeight_inv] at haug
    have hH := two_le_complexMatrixHeight (Nat.succ_pos r) g
    dsimp only [D, b]
    rw [mul_comm (2 : ℝ), mul_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hlen := inverse_log_length_le g⁻¹
  rw [inv_inv] at hlen
  have he : (N : ℝ) * (∑ i, |alpha g i|) - (M : ℝ) * rootPos (alpha g) ≤ (M : ℝ) * Real.log D := by
    have h := mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg (α := ℝ) N)
    change (N : ℝ) * (∑ i, |alpha g i|) ≤ (N : ℝ) *
      ((r + 1 : ℕ) * (Real.log D + rootPos (alpha g))) at h
    push_cast [M] at h ⊢
    nlinarith only [h]
  calc
    _ ≤ C * Real.exp ((N : ℝ) * (∑ i, |alpha g i|) - (M : ℝ) * rootPos (alpha g)) := hb p hp g
    _ ≤ C * Real.exp ((M : ℝ) * Real.log D) := mul_le_mul_of_nonneg_left (Real.exp_monotone he) hC
    _ = C * D ^ M := by rw [Real.exp_nat_mul, Real.exp_log hD]
    _ ≤ C * (b * complexMatrixHeight g) ^ M :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD.le hDle _) hC
    _ = (C * b ^ M) * complexMatrixHeight g ^ M := by rw [mul_pow, mul_assoc]

/-- The canonical Jacquet continuation on `GL₁(ℂ)` equals the original standard vector. -/
theorem continuedJacquet_rankOne (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : Fin (0 + 1) → ℤ)
    (p : Fin (0 + 1) → ℂ) (f : Automorphic.complexStandardKFinite (0 + 1) (characterList l p)) :
    continuedJacquet μ a l p f = f.val := by
  let φ := compactRestriction f.val
  have hφ := compactRestriction_isCompactProfile f.2
  have he := canonicalJacquetFamily_unique μ a l φ hφ (fun q => standardSection q φ)
    (differentiable_standardSection φ) fun q _ g => (openCellIntegral_rankOne μ a (standardSection q φ) g).symm
  change canonicalJacquetFamily μ a l φ hφ p = f.val
  rw [← he]
  exact standardSection_compactRestriction f.2

set_option maxHeartbeats 950000 in
/-- The canonical evaluation is smooth on the full group in every rank greater than one. -/
theorem contMDiff_continuedJacquet_succ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : L') (p : P')
    (f : Std'[l, p]) :
    ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (continuedJacquet μ a l p f) := by
  let ν := complexGeneralLinearHaar (r + 1)
  let S := compactGodementSections ν (addedCharacter l p) (retainedCharacters l p)
  have hspan : Submodule.span ℂ S = Std'[l, p] := by
    rw [characterList_cons]
    exact complexGodementCompactSpanning ν (addedCharacter l p)
      (fun i => characterOfParams (smallerWeights l i) (smallerExponents p i))
  let lift (g : G' → ℂ) (hg : g ∈ Submodule.span ℂ S) : Std'[l, p] := ⟨g, hspan ▸ hg⟩
  have hf : f.val ∈ Submodule.span ℂ S := hspan.symm ▸ f.2
  let J := continuedJacquet μ a l p
  refine Submodule.span_induction (p := fun g hg =>
    ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (J (lift g hg))) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨Φ, f₀, hΦ, hfull, hfinite, rfl⟩
    let u : SmallerProfile l := ⟨compactRestriction f₀.val, compactRestriction_isCompactProfile f₀.2⟩
    have hu : smallerSection p u = f₀.val := standardSection_compactRestriction f₀.2
    have he := complexJacquetGeneratorEvaluation ν μ a l Φ hΦ hfull hfinite u p
    let v : Std'[l, p] := ⟨godementSection ν (addedCharacter l p) Φ (smallerSection p u),
      godementSection_mem_standardKFinite ν l Φ hΦ hfull hfinite u p⟩
    have hv : ∀ hg, lift (godementSection ν (addedCharacter l p) Φ f₀.val) hg = v :=
      fun _ => Subtype.ext (congrArg (godementSection ν (addedCharacter l p) Φ) hu.symm)
    have hm : godementSection ν (addedCharacter l p) Φ f₀.val ∈ S :=
      ⟨Φ, f₀, hΦ, hfull, hfinite, rfl⟩
    rw [hv (Submodule.subset_span hm)]
    change ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (continuedJacquet μ a l p v)
    rw [he]
    let W := canonicalJacquetFamily μ a (smallerWeights l) u.val u.2
    have hw := canonicalJacquetFamily_properties μ a (smallerWeights l) u.val u.2
    obtain ⟨δ, hδ, hB⟩ := hw.2.2.1 (smallerExponents p)
    exact contMDiff_continuedValue ν μ a (characterOfParams (l 0) 0) W (fun q _ => hw.1 q) hB
      (Metric.mem_ball_self hδ) (p 0) _
  · change ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (J 0)
    rw [map_zero]
    exact contMDiff_const
  · intro x y hx hy Ex Ey
    change ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (J (lift x hx + lift y hy))
    rw [map_add]
    exact (contDiff_add (𝕜 := ℝ) (F := ℂ)).contMDiff.comp (Ex.prodMk_space Ey)
  · intro c x hx Ex
    change ContMDiff (matrixModel ℂ (r + 1 + 1)) 𝓘(ℝ, ℂ) ∞ (J (c • lift x hx))
    rw [map_smul]
    exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp (contMDiff_const.prodMk_space Ex)

/-- Canonical complex Jacquet evaluations are smooth and moderately growing for all inducing
characters and compact-finite standard vectors. -/
def ComplexJacquetRegularityStatement : Prop :=
  ∀ (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : Fin (r + 1) → ℤ) (p : Fin (r + 1) → ℂ)
    (f : Automorphic.complexStandardKFinite (r + 1) (characterList l p)),
    ContMDiff (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞ (continuedJacquet μ a l p f) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ g, ‖continuedJacquet μ a l p f g‖ ≤ C * complexMatrixHeight g ^ N

theorem complexJacquetRegularity : ComplexJacquetRegularityStatement := by
  intro r μ a l p f
  have hx := canonicalJacquetFamily_properties μ a l (compactRestriction f.val)
    (compactRestriction_isCompactProfile f.2)
  obtain ⟨δ, hδ, hB⟩ := hx.2.2.1 p
  refine ⟨?_, exists_height_bound_of_uniformGauge hB (Metric.mem_ball_self hδ)⟩
  cases r with
  | zero =>
    rw [continuedJacquet_rankOne]
    exact f.2.1.1
  | succ r => exact contMDiff_continuedJacquet_succ μ a l p f

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
