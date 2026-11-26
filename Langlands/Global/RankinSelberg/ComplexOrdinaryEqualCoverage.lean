import Langlands.Global.RankinSelberg.ComplexEqualSquareTrace
import Langlands.Global.RankinSelberg.ComplexOrdinaryAdjacentCoverage
import Langlands.Global.RankinSelberg.ComplexSquareGaussianRowSplit
import Langlands.Global.RankinSelberg.ComplexLocalEqualGrowthStep

/-! # Equal-rank Gaussian coverage from adjacent ordinary coverage -/

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.GodementJacquet Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open ComplexCompactProfileFamily (characterList)
open ComplexGodement (addedCharacter retainedCharacters characterList_cons)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementContinuedModel (complexGodementContinuedModel)
open ComplexGodementGaussianPolynomial (standardMatrixTest)
open ComplexJacquet
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner complexJacquetNonzero
  exists_smallerQuotientData)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)
open ComplexAdjacentUnfolding (complexAdjacent_groupHaar_rightInvariant whittakerVector)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

section SquareSum

variable {r : ℕ}
local notation "n" => (r + 1 : ℕ)
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "KF[" es "]" => complexStandardKFinite n es

private theorem integrable_leftShift_matrixIntegrand (μ : Measure G) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) {b : G → ℂ} (hc : Continuous b) {C : ℝ} (hC : 0 ≤ C) {M : ℕ}
    (h : ∀ g, ‖b g‖ ≤ C * complexMatrixHeight g ^ M) (x : G)
    (Φ : 𝓢(Mat, ℂ)) (s : ℂ) (hs : (n : ℝ) + M ≤ (s + (r : ℂ) / 2 + d.exponent).re) :
    Integrable (complexJacquetMatrixIntegrand d (fun g => b (x * g)) Φ s) μ := by
  let H (g : G) := max 1 (complexMatrixHeight g)
  let A := complexWeightedMatrixTest d.character Φ (s + (r : ℂ) / 2)
  have hAc : Continuous A := ((Φ.continuous.comp Units.continuous_val).mul
    (Units.continuous_val.comp (d.character.continuous.comp continuous_complexDeterminant))).mul
      (continuous_complexDetPower _)
  have hMajor := complexLocalMatrixMajorant n M μ d Φ (s + (r : ℂ) / 2) hs
  have hInt : Integrable (fun g => (C * H x ^ M) * (H g ^ M * ‖A g‖)) μ := hMajor.const_mul _
  refine hInt.mono' (hAc.mul (hc.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    (ae_of_all _ fun g => ?_)
  have hBound : ‖b (x * g)‖ ≤ (C * H x ^ M) * H g ^ M := by
    refine (h (x * g)).trans ?_
    rw [mul_assoc C, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (complexMatrixHeight_nonneg _)
      ((le_max_right 1 _).trans (max_complexMatrixHeight_mul_le x g)) _) hC
  change ‖A g * b (x * g)‖ ≤ (C * H x ^ M) * (H g ^ M * ‖A g‖)
  rw [norm_mul]
  calc
    _ ≤ ‖A g‖ * ((C * H x ^ M) * H g ^ M) := mul_le_mul_of_nonneg_left hBound (norm_nonneg _)
    _ = _ := by ring

private theorem squareConvolutionTrace_eq_sum {l : ℕ} (μ : Measure G) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData) {a : ℂˣ}
    (B : KF[List.ofFn e] →ₗ[ℂ] (G → ℂ)) (hB : IsComplexWhittakerIntertwiner r (List.ofFn e) a B)
    (hInj : Function.Injective B) (f : KF[List.ofFn e])
    (Ψ : 𝓢(Mat, ℂ)) (Φ : Fin l → 𝓢(Mat, ℂ))
    (he : ∀ X : Mat, Ψ X = ∑ j, Φ j X)
    (F : ℂ → KF[List.ofFn e]) (Fj : Fin l → ℂ → KF[List.ofFn e])
    (hF : HasSquareConvolutionTrace μ d e B Ψ f F)
    (hFj : ∀ j, HasSquareConvolutionTrace μ d e B (Φ j) f (Fj j)) :
    ∀ s, F s = ∑ j, Fj j s := by
  obtain ⟨b, hb⟩ := hF.2
  choose bj hbj using fun j => (hFj j).2
  obtain ⟨b₀, hb₀⟩ := (finite_range bj).bddAbove
  obtain ⟨C, M, hM⟩ := hB.2.2.1 f
  let L (s : ℂ) := (complexPairLFactor [d] (List.ofFn e)).denominator s
  let β := max (max b b₀) ((n : ℝ) + M - ((r : ℂ) / 2 + d.exponent).re)
  have hEq (s : ℂ) (hs : β < s.re) (x : G) : B (F s) x = ∑ j, B (Fj j s) x := by
    let K (φ : 𝓢(Mat, ℂ)) := complexJacquetMatrixIntegrand d (fun g => B f (x * g)) φ s
    have hI (j : Fin l) : Integrable (K (Φ j)) μ := by
      refine integrable_leftShift_matrixIntegrand μ d (hB.2.1 f).continuous (le_max_right C 0)
        (fun g => (hM g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pow_nonneg (complexMatrixHeight_nonneg _) _))) x (Φ j) s ?_
      have hh := (le_max_right _ _ : (n : ℝ) + M - ((r : ℂ) / 2 + d.exponent).re ≤ β).trans_lt hs
      rw [add_assoc, Complex.add_re]
      linarith
    have hK (g : G) : K Ψ g = ∑ j, K (Φ j) g := by
      simp only [K, complexJacquetMatrixIntegrand, he g.val, Finset.sum_mul]
    rw [hb s ((le_max_left b b₀).trans_lt ((le_max_left _ _).trans_lt hs)) x]
    change L s * (∫ g, K Ψ g ∂μ) = _
    simp_rw [hK]
    rw [integral_finsetSum Finset.univ (fun j _ => hI j), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (hbj j s ((hb₀ (mem_range_self j)).trans_lt
      ((le_max_right b b₀).trans_lt ((le_max_left _ _).trans_lt hs))) x).symm
  have polydiff (φ : 𝓢(Mat, ℂ)) (F₀ : ℂ → KF[List.ofFn e])
      (h₀ : HasSquareConvolutionTrace μ d e B φ f F₀) (x : G) :
      Differentiable ℂ (fun s => B (F₀ s) x) := by
    obtain ⟨k, P, v, hv⟩ := h₀.1
    simp_rw [hv, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Differentiable.fun_sum fun j _ => (P j).differentiable.mul_const _
  intro s
  apply hInj
  funext x
  have hR : Differentiable ℂ (fun w => ∑ j, B (Fj j w) x) :=
    Differentiable.fun_sum fun j _ => polydiff (Φ j) (Fj j) (hFj j) x
  let z₀ : ℂ := ((β + 1 : ℝ) : ℂ)
  have hz₀ : β < z₀.re := by simpa only [z₀, Complex.ofReal_re] using lt_add_one β
  have h := AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => (polydiff Ψ F hF x).analyticAt w)
    (fun w _ => hR.analyticAt w) (z₀ := z₀) (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀] with w hw
      exact hEq w hw x)
  simpa only [map_sum, Finset.sum_apply] using congrFun h s

end SquareSum

/-- Adjacent ordinary coverage for the opposite list and the retained list gives equal-rank
standard Gaussian coverage after adjoining a character to the retained list. -/
def ComplexOrdinaryEqualCoverageStepStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData),
    ds.length = r + 1 → es.length = r + 2 →
    IsIrreducibleGKModule (complexStandardRep (r + 2) (d :: ds)) (complexStandardLie (r + 2) (d :: ds)) →
    IsIrreducibleGKModule (complexStandardRep (r + 2) es) (complexStandardLie (r + 2) es) →
    ComplexAdjacentCoverageAtRank r (-a) →
    ∀ D : ComplexQuotientMeasureData (r + 1),
      HasCoveringOrdinaryNormalizations
        (ComplexEqualPolynomialGeneration.gaussianEqualIntegral (r + 1) (d :: ds) es a (2 * Real.pi) D)
        (complexPairLFactor (d :: ds) es)

set_option maxHeartbeats 2000000 in
theorem complexOrdinaryEqualCoverageStep : ComplexOrdinaryEqualCoverageStepStatement := by
  intro r a d ds es hd he hId hIe hCover D s₀
  obtain ⟨k, p, rfl⟩ := exists_characterList es he
  let n := r + 2
  let G := Langlands.GeneralLinear n ℂ
  let e : Fin n → ComplexCharacterData := fun j => characterOfParams (k j) (p j)
  let es := List.ofFn e
  have hCons : (d :: ds).length = r + 2 := by rw [List.length_cons, hd]
  have hUnl := ((complexStandardIrreducibilityUnlinked n (d :: ds) hCons).mp hId).sublist (List.sublist_cons_self d ds)
  have hIds := (complexStandardIrreducibilityUnlinked (r + 1) ds hd).mpr hUnl
  let D₁ := Classical.choice (exists_smallerQuotientData (r := r))
  let μ := complexSelfDualMeasure a
  let B : complexStandardKFinite n es →ₗ[ℂ] (G → ℂ) := continuedJacquet μ a k p
  have hB : IsComplexWhittakerIntertwiner (r + 1) es (-a) B := complexJacquetIntertwiner (r + 1) μ a k p
  have hB₀ : B ≠ 0 := by
    obtain ⟨v, hv⟩ := complexJacquetNonzero (r + 1) μ a k p
    intro h
    exact hv (by change B v 1 = 0; rw [h]; rfl)
  have hRange : complexWhittakerModel (r + 1) es (-a) = B.range :=
    (complexJacquetMultiplicityOne (r + 1) μ a k p).2
  obtain ⟨⟨V, U₀⟩, N₀, hN₀⟩ := hCover es ds List.length_ofFn hd hIe hIds D₁ s₀
  let U : complexWhittakerModel r ds a := ⟨U₀.val, by simpa only [neg_neg] using U₀.2⟩
  have hV : V.val ∈ B.range :=
    (congrArg (fun M : Submodule ℂ (G → ℂ) => V.val ∈ M) hRange).mp V.2
  obtain ⟨v₀, hv₀⟩ := hV
  obtain ⟨A, hA⟩ := exists_complexUnequalNormalizationLinear (Nat.lt_succ_self r) D₁ (-a) es ds
    List.length_ofFn hd U₀ B hB
  let ev := (LinearMap.proj s₀).comp A
  have hev₀ : ev v₀ ≠ 0 := by
    have hA₀ := hA v₀
    rw [hv₀] at hA₀
    obtain ⟨N, hN⟩ := hA₀
    obtain ⟨σ, hσ⟩ := complexPairLFactor_denominator_ne_zero es ds
    have hEq := N.value_eq_of_factor_ne_zero N₀ ⟨σ, fun s hs => inv_ne_zero (hσ s hs)⟩
    change A v₀ s₀ ≠ 0
    rw [hN, hEq]
    exact hN₀
  have hev : ev ≠ 0 := fun h => hev₀ (by rw [h]; rfl)
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D₁.groupHaar.IsHaarMeasure := D₁.groupHaar_isHaar
  let : D₁.groupHaar.IsMulRightInvariant := complexAdjacent_groupHaar_rightInvariant D₁
  obtain ⟨Ψ, P, f, F, hΨ, hF, hF₀⟩ := exists_squareConvolution_trace_ne_zero
    D.groupHaar d e hIe (-a) B hB hB₀ s₀ ev hev
  obtain ⟨l, pj, φ, hφ, hSplit⟩ := complexSquareGaussianRowSplit P
  let Φ j := operatorToEntry (standardMatrixTest (pj j))
  let Ψj (j : Fin l) := complexMatrixEntryToOperator (complexSquareProductSchwartz (Φ j) (φ j))
  have hProd (j : Fin l) : (Ψj j : Matrix (Fin n) (Fin n) ℂ → ℂ) = complexSquareProductTest (Φ j) (φ j) :=
    funext (complexSquareProductSchwartz_apply _ _)
  choose Pj hPj using fun j => standardSquareProduct_polynomialGaussian (pj j) (φ j) (hφ j)
  have hConv (j : Fin l) : ∃ Fj, HasSquareConvolutionTrace D.groupHaar d e B (Ψj j) f Fj := by
    obtain ⟨Fj, hFj, hTrace⟩ := complexSquareZetaConvolution D.groupHaar d e (Ψj j) (Pj j)
      ((hProd j).trans (hPj j)) (-a) B hB f
    exact ⟨Fj, hFj.1, hTrace⟩
  choose Fj hFj using hConv
  have hSum := squareConvolutionTrace_eq_sum D.groupHaar d e B hB (hB.injective_of_irreducible hB₀ hIe)
    f Ψ Ψj (fun X => (congrFun hΨ X).trans (by simpa only [hProd] using hSplit X)) F Fj hF hFj s₀
  obtain ⟨c, hc, hEqual⟩ := complexEqualSquareTrace D D₁ a
  obtain ⟨l₀, q, hList⟩ := exists_characterList (d :: ds) hCons
  have hChars := List.cons.inj ((characterList_cons l₀ q).symm.trans hList)
  let U' : complexWhittakerModel r (retainedCharacters l₀ q) (-(-a)) := ⟨U₀.val, hChars.2.symm ▸ U₀.2⟩
  let W (j : Fin l) (g : G) := continuedValue D₁.groupHaar (complexSelfDualMeasure (-a)) d (-a) (Φ j) U.val g 0
  have hW (j : Fin l) : W j ∈ complexWhittakerModel (r + 1) (d :: ds) a := by
    have hI : IsIrreducibleGKModule (complexStandardRep n (characterList l₀ q))
        (complexStandardLie n (characterList l₀ q)) := hList.symm ▸ hId
    have hMem := complexGodementContinuedModel D₁.groupHaar (complexSelfDualMeasure (-a)) (-a) l₀ q hI
      (standardMatrixTest (pj j)) (finiteDimensional_translateTest_standardMatrixTest (pj j)) U'
    simpa only [hList, hChars.1, neg_neg, U', U, W, Φ] using hMem
  have hNorm (j : Fin l) := hEqual d ds e hd hUnl U B hB (pj j) (φ j) (Ψj j) (hProd j) f (Fj j) (hFj j) A hA
  choose N hN using hNorm
  have hc₀ : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  by_contra! hz
  have hZero (j : Fin l) : ev (Fj j s₀) = 0 := by
    have hj := hz (⟨W j, hW j⟩, whittakerVector hB f, ⟨φ j, hφ j⟩) (N j)
    rw [hN j s₀] at hj
    exact (mul_eq_zero.mp hj).resolve_left
      (mul_ne_zero (d.character ((-1 : ℂˣ) ^ (r + 1))).ne_zero (inv_ne_zero hc₀))
  apply hF₀
  rw [hSum, map_sum]
  exact Finset.sum_eq_zero fun j _ => hZero j

end Langlands.Global.RankinSelbergGlobal
