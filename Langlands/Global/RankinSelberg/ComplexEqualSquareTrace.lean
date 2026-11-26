import Langlands.Global.RankinSelberg.ComplexEqualSquareTraceChamber
import Langlands.Global.RankinSelberg.ComplexEqualContinuedGodementFamily
import Langlands.Global.RankinSelberg.ComplexGodementUnlinkedFamily
import Langlands.Global.RankinSelberg.ComplexStandardSplitGodementTests
import Langlands.Global.RankinSelberg.ComplexLocalEqualChamberUnfolding
import Langlands.Global.RankinSelberg.ComplexGodementRecursionComparison

/-! # The entire equal-rank normalization of a separated square convolution -/

noncomputable section

open Filter MeasureTheory Metric Set
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open scoped Matrix.Norms.Operator NNReal SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GodementJacquet
open Langlands.LocalFactor.Archimedean
open ComplexAdjacentUnfolding (whittakerVector complexAdjacent_groupHaar_rightInvariant)
open ComplexGodement (shiftedCharacter)
open ComplexGodementAddedCharacter (continuedValue continuedValue_eq_signed_recursion)
open ComplexGodementGaussianPolynomial (Coordinates standardMatrixTest)
open ComplexUnequalFamily (HasLeftCharacter)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => (r + 1 : ℕ)
local notation "n" => (r + 1 + 1 : ℕ)
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Row" => Fin n → ℂ
local notation "gap" => Nat.lt_succ_self r
local notation "KF[" es "]" => complexStandardKFinite n es

private theorem shiftedCharacter_zero (d : ComplexCharacterData) : shiftedCharacter d 0 = d := by
  rw [shiftedCharacter, add_zero, characterOfParams_eta]

/-- For a separated square test, the entire equal-rank normalization is a nonzero scalar
multiple of the lower normalized adjacent functional applied to the square convolution.
The positive Haar scalar depends only on the two quotient data and the additive scale. -/
def ComplexEqualSquareTraceStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r) (a : ℂˣ),
    ∃ c : ℝ≥0, 0 < c ∧
    ∀ (d : ComplexCharacterData) (ds : List ComplexCharacterData) (e : Fin n → ComplexCharacterData),
      ds.length = m → IsComplexUnlinked ds →
    ∀ (U : complexWhittakerModel r ds a) (B : KF[List.ofFn e] →ₗ[ℂ] (G → ℂ)),
      IsComplexWhittakerIntertwiner (r + 1) (List.ofFn e) (-a) B →
    ∀ (p : MvPolynomial (Coordinates m n) ℂ) (φ : 𝓢(Row, ℂ)) (Ψ : 𝓢(Mat, ℂ)),
      (Ψ : Mat → ℂ) = complexSquareProductTest (operatorToEntry (standardMatrixTest p)) φ →
    ∀ (f : KF[List.ofFn e]) (F : ℂ → KF[List.ofFn e]), HasSquareConvolutionTrace D.groupHaar d e B Ψ f F →
    ∀ A : KF[List.ofFn e] →ₗ[ℂ] (ℂ → ℂ),
      (∀ v, ∃ N : OrdinaryIntegralNormalization (complexUnequalIntegral gap D₁ (B v) U.val)
        (fun s => ((complexPairLFactor (List.ofFn e) ds).denominator s)⁻¹), A v = N.value) →
    let W (g : G) := continuedValue D₁.groupHaar (complexSelfDualMeasure (-a)) d (-a)
      (operatorToEntry (standardMatrixTest p)) U.val g 0
    ∃ N : OrdinaryIntegralNormalization (complexEqualIntegral D W (B f) φ)
      (fun s => ((complexPairLFactor (d :: ds) (List.ofFn e)).denominator s)⁻¹),
      ∀ s, N.value s = ((d.character ((-1 : ℂˣ) ^ m) : ℂ) * (c : ℂ)⁻¹) * A (F s) s

set_option maxHeartbeats 2200000 in
theorem complexEqualSquareTrace : ComplexEqualSquareTraceStatement (r := r) := by
  intro D D₁ a
  obtain ⟨c, hc, hChamber⟩ := complexLocalEqualChamberUnfolding (r := r) D D₁ a
  refine ⟨c, hc, ?_⟩
  intro d ds e hd hUnl U B hB p φ Ψ hΨ f F hF A hA W₀
  have hUc : Continuous U.val := (contMDiff_of_mem_complexWhittakerModel U.2).continuous
  let es := List.ofFn e
  let V := whittakerVector hB f
  let Φ := operatorToEntry (standardMatrixTest p)
  let ν := D₁.groupHaar
  let μ := complexSelfDualMeasure (-a)
  let : ν.IsHaarMeasure := D₁.groupHaar_isHaar
  let : ν.IsMulRightInvariant := complexAdjacent_groupHaar_rightInvariant D₁
  let W (z : ℂ) (g : G) := continuedValue ν μ d (-a) Φ U.val g z
  let U' : complexWhittakerModel r ds (-(-a)) := ⟨U, by simpa only [neg_neg] using U.2⟩
  have hLeft (z : ℂ) : HasLeftCharacter a (W z) := by
    have hh := (complexGodementUnlinkedFamily ν μ (-a) d ds hd hUnl U' (standardMatrixTest p)
      (finiteDimensional_translateTest_standardMatrixTest p)).2 z
    simpa only [neg_neg, U', W, Φ] using hh
  obtain ⟨τ, σ, hTrace⟩ := complexEqualSquareTraceChamber a D D₁ d ds e U B hB Ψ f F hF A hA
  obtain ⟨Φd, hΦd⟩ := exists_schwartz_complexRectangularFourier (-a) Φ
  obtain ⟨φd, hφd⟩ := exists_schwartz_complexFourierTransform a φ
  obtain ⟨τ', σ', hOrd⟩ := (hChamber d ds es hd List.length_ofFn U V Φ Φd φ φd hΦd hφd).1
  let b := max τ τ'
  let R := |b| + 3
  let S := ball (0 : ℂ) R
  have hS : IsOpen S := isOpen_ball
  have hS₀ : (0 : ℂ) ∈ S := mem_ball_self (by dsimp [R]; positivity)
  obtain ⟨σ₀, _, hJ⟩ := complexEqualContinuedGodementFamily D D₁ a d ds es U V Φ φ
    ⟨0, fun z _ => hLeft z⟩ R
  change DifferentiableOn ℂ (fun x : ℂ × ℂ => complexEqualIntegral D (W x.1) (B f) φ x.2)
    (S ×ˢ {w : ℂ | σ₀ < w.re}) at hJ
  let γ : ℂ := d.character ((-1 : ℂˣ) ^ m)
  let C := γ * (c : ℂ)⁻¹
  have hc₀ : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hUb := complexLocalWhittakerSimpleRootBound_of_uniformGrowth complexLocalWhittakerUniformGrowth
    r ds hd a U.val U.2
  have hRec (z : ℂ) (g : G) : W z g = γ *
      complexJacquetRecursion a D₁ Φ U.val (shiftedCharacter d z).character.toMonoidHom g := by
    have h := continuedValue_eq_signed_recursion (r := r) (-a) D₁ d Φ hUc
      (fun v x => by simpa only [neg_neg, complexWhittakerCharacter, Langlands.HarmonicAnalysis.unipotentFourierSum]
        using complexWhittakerModel_left_equivariant U.2 v.val v.2 x)
      hUb g z
    simpa only [W, γ, neg_neg, shiftedCharacter] using h
  let I (z s : ℂ) := equalDoubleDenominator d ds es z s * complexEqualIntegral D (W z) (B f) φ s
  have hCh (z s : ℂ) (hz : b < z.re) (hs : max σ σ' < s.re) : I z s = C * A (F (s + z)) s := by
    have hT := hTrace z s ((le_max_left τ τ').trans_lt hz) ((le_max_left σ σ').trans_lt hs)
    have he := hOrd z s ((le_max_right τ τ').trans_lt hz) ((le_max_right σ σ').trans_lt hs)
    let Vz := complexJacquetRecursion a D₁ Φ U.val (shiftedCharacter d z).character.toMonoidHom
    change (c : ℂ) * complexEqualIntegral D Vz (B f) φ s = _ at he
    have hScale := complexEqualIntegral_scale_left_of_eq D γ Vz (W z) (B f) φ s (fun g => (hRec z g).symm)
    have hEntry : complexEqualUnfoldedIntegral D.groupHaar D₁ (shiftedCharacter d z).character Ψ U.val (B f) s =
        (c : ℂ) * complexEqualIntegral D Vz (B f) φ s := by
      rw [hΨ]
      exact he.symm
    rw [hEntry] at hT
    change equalDoubleDenominator d ds es z s * complexEqualIntegral D (W z) (B f) φ s = _
    rw [← hScale, ← hT]
    dsimp only [C, es]
    field_simp [hc₀]
  obtain ⟨l, P, v, hPoly⟩ := hF.1
  let s₁ : ℂ := ((max b 0 + 1 : ℝ) : ℂ)
  have hs₁ : s₁ ∈ S ∩ {z : ℂ | b < z.re} := by
    refine ⟨?_, ?_⟩
    · change s₁ ∈ ball (0 : ℂ) R
      rw [mem_ball, dist_zero_right, show s₁ = _ from rfl, Complex.norm_real, Real.norm_of_nonneg]
      · dsimp only [R]
        linarith [max_le (le_abs_self b) (abs_nonneg b)]
      · linarith [le_max_right b (0 : ℝ)]
    · change b < (((max b 0 + 1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]
      linarith [le_max_left b (0 : ℝ)]
  have hEquality (s : ℂ) (hs : max (max σ σ') σ₀ < s.re) : I 0 s = C * A (F s) s := by
    have hInt : DifferentiableOn ℂ (fun z => complexEqualIntegral D (W z) (B f) φ s) S := by
      have hm : MapsTo (fun z : ℂ => (z, s)) S (S ×ˢ {w : ℂ | σ₀ < w.re}) :=
        fun z hz => ⟨hz, (le_max_right _ _).trans_lt hs⟩
      have hPair : Differentiable ℂ (fun z : ℂ => (z, s)) :=
        differentiable_id.prodMk (differentiable_const s)
      have hPairOn : DifferentiableOn ℂ (fun z : ℂ => (z, s)) S := hPair.differentiableOn
      simpa only [Function.comp_def] using (hJ.comp hPairOn hm)
    have hDen : Differentiable ℂ (fun z => equalDoubleDenominator d ds es z s) :=
      (((complexPairLFactor [d] es).entire.comp (differentiable_id.const_add s)).const_mul _)
    have hI : DifferentiableOn ℂ (fun z => I z s) S := hDen.differentiableOn.mul hInt
    have hRhs : Differentiable ℂ (fun z => C * A (F (s + z)) s) := by
      simp_rw [hPoly, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact (Differentiable.fun_sum fun j _ => ((P j).differentiable.comp
        (differentiable_id.const_add s)).mul_const _).const_mul C
    have hNear : ∀ᶠ z in 𝓝 s₁, z ∈ S ∩ {z : ℂ | b < z.re} :=
      (hS.inter (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds hs₁
    have hEq := hI.analyticOnNhd hS |>.eqOn_of_preconnected_of_eventuallyEq
      (fun z _ => hRhs.analyticAt z) (convex_ball _ _).isPreconnected hs₁.1
      (hNear.mono fun z hz => hCh z s hz.2 ((le_max_left _ _).trans_lt hs)) hS₀
    simpa only [add_zero] using hEq
  let Y (s : ℂ) := C * A (F s) s
  have hY : Differentiable ℂ Y := by
    have hAd (j : Fin l) : Differentiable ℂ (A (v j)) := by
      obtain ⟨N, hN⟩ := hA (v j)
      rw [hN]
      exact fun s => (N.analytic s (mem_univ _)).differentiableAt
    dsimp only [Y]
    simp_rw [hPoly, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (Differentiable.fun_sum fun j _ => (P j).differentiable.mul (hAd j)).const_mul C
  obtain ⟨bL, hbL⟩ := complexPairLFactor_denominator_ne_zero (d :: ds) es
  refine ⟨⟨Y, fun s _ => hY.analyticAt s, max (max (max σ σ') σ₀) bL, fun s hs => ?_⟩, fun _ => rfl⟩
  have he := hEquality s ((le_max_left _ _).trans_lt hs)
  have hn := hbL s ((le_max_right _ _).trans_lt hs)
  change equalDoubleDenominator d ds es 0 s * complexEqualIntegral D (W 0) (B f) φ s = Y s at he
  rw [equalDoubleDenominator_eq_pair, shiftedCharacter_zero] at he
  change complexEqualIntegral D (W 0) (B f) φ s =
    Y s * ((complexPairLFactor (d :: ds) es).denominator s)⁻¹
  rw [← he, mul_comm ((complexPairLFactor (d :: ds) es).denominator s), mul_assoc, mul_inv_cancel₀ hn, mul_one]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
