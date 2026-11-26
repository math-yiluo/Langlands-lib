import Langlands.Global.RankinSelberg.ComplexAdjacentSquareTrace
import Langlands.Global.RankinSelberg.ComplexStandardSplitGodementTests
import Langlands.Global.RankinSelberg.ComplexOrdinaryAdjacentPolynomial

/-! # Adjacent ordinary coverage from equal-rank Gaussian coverage -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open ComplexCompactProfileFamily (characterList)
open ComplexGodement (addedCharacter retainedCharacters characterList_cons)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementColumnProduct (columnProduct)
open ComplexGodementContinuedModel (complexGodementContinuedModel)
open ComplexGodementGaussianPolynomial (Coordinates)
open ComplexSquareZeta (squarePolynomialGaussian)
open ComplexEqualPolynomialGeneration (gaussianEqualIntegral)
open ComplexAdjacentUnfolding (complexAdjacentSquareTrace whittakerVector exists_complexEqualNormalizationLinear
  complexAdjacent_groupHaar_rightInvariant quotient_sFinite)
open ComplexJacquet (squareConvolutionSpan HasSquareConvolutionTrace complexSquareConvolutionGeneration)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner complexJacquetNonzero)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => (r + 1 : ℕ)
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear (m + 1) ℂ
local notation "Mat" => Matrix (Fin m) (Fin m) ℂ
local notation "KF[" es "]" => complexStandardKFinite m es
local notation "gap" => Nat.lt_succ_self r

/-- Every complex Whittaker model of the prescribed length has a nonzero canonical value. -/
theorem complexWhittakerModel_ne_bot_of_length (ds : List ComplexCharacterData) (hds : ds.length = m)
    (a : ℂˣ) : complexWhittakerModel r ds a ≠ ⊥ := by
  obtain ⟨k, p, rfl⟩ := exists_characterList ds hds
  let μ := complexSelfDualMeasure (-a)
  obtain ⟨v, hv⟩ := complexJacquetNonzero r μ (-a) k p
  have hR := (complexJacquetMultiplicityOne r μ (-a) k p).2
  rw [neg_neg] at hR
  intro h
  have hV : continuedJacquet μ (-a) k p v ∈ complexWhittakerModel r (characterList k p) a := by
    rw [hR]
    exact ⟨v, rfl⟩
  exact hv (congrFun ((Submodule.mem_bot ℂ).mp (h ▸ hV)) 1)

/-- A nonzero linear functional is nonzero on a normalized square convolution generator
at the chosen spectral point. -/
theorem exists_squareConvolution_trace_ne_zero
    (μ : Measure H) [μ.IsHaarMeasure] (d : ComplexCharacterData) (e : Fin m → ComplexCharacterData)
    (hirr : IsIrreducibleGKModule (complexStandardRep m (List.ofFn e)) (complexStandardLie m (List.ofFn e)))
    (a : ℂˣ) (B : KF[List.ofFn e] →ₗ[ℂ] (H → ℂ)) (hB : IsComplexWhittakerIntertwiner r (List.ofFn e) a B)
    (hB₀ : B ≠ 0) (s₀ : ℂ) (A : KF[List.ofFn e] →ₗ[ℂ] ℂ) (hA : A ≠ 0) :
    ∃ (Φ : 𝓢(Mat, ℂ)) (P : MvPolynomial (Coordinates m m) ℂ) (f : KF[List.ofFn e]) (F : ℂ → KF[List.ofFn e]),
      (Φ : Mat → ℂ) = squarePolynomialGaussian P ∧ HasSquareConvolutionTrace μ d e B Φ f F ∧ A (F s₀) ≠ 0 := by
  by_contra! h
  have hKer : squareConvolutionSpan μ d e B s₀ ≤ LinearMap.ker A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Φ, P, f, F, hΦ, hF, rfl⟩
    exact LinearMap.mem_ker.mpr (h Φ P f F hΦ hF)
  rw [complexSquareConvolutionGeneration μ d e hirr a B hB hB₀ s₀] at hKer
  exact hA (LinearMap.ext fun v => LinearMap.mem_ker.mp (hKer (Submodule.mem_top : v ∈ ⊤)))

/-- Pointwise normalized coverage for equal-rank ordinary integrals with standard Gaussian
row tests, for all irreducible lists of the indicated rank. -/
def ComplexEqualGaussianCoverageAtRank (r : ℕ) (a : ℂˣ) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
    IsIrreducibleGKModule (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds) →
    IsIrreducibleGKModule (complexStandardRep (r + 1) es) (complexStandardLie (r + 1) es) →
    ∀ D : ComplexQuotientMeasureData r,
      HasCoveringOrdinaryNormalizations (gaussianEqualIntegral r ds es a (2 * Real.pi) D) (complexPairLFactor ds es)

/-- Pointwise normalized coverage for ordinary adjacent-rank pairs of irreducible lists. -/
def ComplexAdjacentCoverageAtRank (r : ℕ) (a : ℂˣ) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 2 → es.length = r + 1 →
    IsIrreducibleGKModule (complexStandardRep (r + 2) ds) (complexStandardLie (r + 2) ds) →
    IsIrreducibleGKModule (complexStandardRep (r + 1) es) (complexStandardLie (r + 1) es) →
    ∀ D : ComplexQuotientMeasureData r,
      HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest (Nat.lt_succ_self r) ds es a D) (complexPairLFactor ds es)

/-- At unit-modulus trace scale, equal-rank Gaussian coverage for the retained and opposite
lists lifts to adjacent-rank ordinary coverage for the enlarged and opposite lists. -/
def ComplexOrdinaryAdjacentCoverageStepStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ), ‖(a : ℂ)‖ = 1 →
  ∀ (d : ComplexCharacterData) (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
    IsIrreducibleGKModule (complexStandardRep (r + 2) (d :: ds)) (complexStandardLie (r + 2) (d :: ds)) →
    IsIrreducibleGKModule (complexStandardRep (r + 1) es) (complexStandardLie (r + 1) es) →
    ∀ D : ComplexQuotientMeasureData r,
      HasCoveringOrdinaryNormalizations (gaussianEqualIntegral r ds es (-a) (2 * Real.pi) D) (complexPairLFactor ds es) →
      HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest (Nat.lt_succ_self r) (d :: ds) es (-a) D)
        (complexPairLFactor (d :: ds) es)

set_option maxHeartbeats 1150000 in
theorem complexOrdinaryAdjacentCoverageStep : ComplexOrdinaryAdjacentCoverageStepStatement := by
  intro r a ha d ds es hd he hId hIe D hCover s₀
  obtain ⟨k, p, rfl⟩ := exists_characterList es he
  let e : Fin (r + 1) → ComplexCharacterData := fun i => characterOfParams (k i) (p i)
  let es := List.ofFn e
  let μ := complexSelfDualMeasure (-a)
  let B : complexStandardKFinite (r + 1) es →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℂ → ℂ) :=
    continuedJacquet μ (-a) k p
  have hB : IsComplexWhittakerIntertwiner r es a B := by
    simpa only [B, es, e, characterList, neg_neg] using complexJacquetIntertwiner r μ (-a) k p
  have hB₀ : B ≠ 0 := by
    obtain ⟨v, hv⟩ := complexJacquetNonzero r μ (-a) k p
    intro h
    exact hv (by change B v 1 = 0; rw [h]; rfl)
  have hRange : complexWhittakerModel r es a = B.range := by
    simpa only [B, es, e, characterList, neg_neg] using (complexJacquetMultiplicityOne r μ (-a) k p).2
  obtain ⟨⟨U, V, ψ⟩, N₀, hN₀⟩ := hCover s₀
  have hV : V.val ∈ complexWhittakerModel r es a := by
    simpa only [es, e, characterList, neg_neg] using V.2
  rw [hRange] at hV
  obtain ⟨v₀, hv₀⟩ := hV
  obtain ⟨φ, hφ, hFourier⟩ := exists_standard_splitRowTransform_preimage a ha ψ.val ψ.2
  obtain ⟨A, hA⟩ := exists_complexEqualNormalizationLinear D a ds es hd List.length_ofFn U
    (ComplexAdjacentUnfolding.splitRowTransform a φ) B hB
  let ev := (LinearMap.proj s₀).comp A
  have hev₀ : ev v₀ ≠ 0 := by
    have hA₀ := hA v₀
    rw [hv₀, hFourier] at hA₀
    obtain ⟨N, hN⟩ := hA₀
    obtain ⟨σ, hσ⟩ := complexPairLFactor_denominator_ne_zero ds es
    have hEq := N.value_eq_of_factor_ne_zero N₀ ⟨σ, fun s hs => inv_ne_zero (hσ s hs)⟩
    change A v₀ s₀ ≠ 0
    rw [hN, hEq]
    exact hN₀
  have hev : ev ≠ 0 := fun h => hev₀ (by rw [h]; rfl)
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.IsMulRightInvariant := complexAdjacent_groupHaar_rightInvariant D
  let : SFinite D.measure := quotient_sFinite D
  obtain ⟨Φ, P, f, F, hΦ, hF, hF₀⟩ := exists_squareConvolution_trace_ne_zero
    D.groupHaar d e hIe a B hB hB₀ s₀ ev hev
  obtain ⟨N, hN⟩ := complexAdjacentSquareTrace D a d ds e hd U B hB Φ φ f F hF A hA
  let W (g : Langlands.GeneralLinear (r + 2) ℂ) := continuedValue D.groupHaar (complexSelfDualMeasure a) d a
    (operatorToEntry (columnProduct Φ φ)) U.val g 0
  obtain ⟨l, q, hList⟩ := exists_characterList (n := r + 2) (d :: ds) (by rw [List.length_cons, hd])
  have hc := List.cons.inj ((characterList_cons l q).symm.trans hList)
  let U' : complexWhittakerModel r (retainedCharacters l q) (-a) := ⟨U.val, hc.2.symm ▸ U.2⟩
  have hW : W ∈ complexWhittakerModel (r + 1) (d :: ds) (-a) := by
    have hI : IsIrreducibleGKModule (complexStandardRep (r + 2) (characterList l q))
        (complexStandardLie (r + 2) (characterList l q)) := hList.symm ▸ hId
    have hW₀ := complexGodementContinuedModel D.groupHaar (complexSelfDualMeasure a) a l q hI
      (columnProduct Φ φ) (complexStandardSplitGodementTest r Φ P hΦ φ hφ) U'
    simpa only [hList, hc.1, U', W] using hW₀
  exact ⟨(⟨W, hW⟩, ⟨B f, by
    simpa only [es, e, characterList, neg_neg, ComplexAdjacentUnfolding.whittakerVector_val]
      using (whittakerVector hB f).2⟩), N,
    by rw [hN]; exact mul_ne_zero (d.character ((-1 : ℂˣ) ^ (r + 1))).ne_zero hF₀⟩

end Langlands.Global.RankinSelbergGlobal
