import Langlands.Global.RankinSelberg.ComplexOrdinaryCharacterTransport
import Langlands.Global.RankinSelberg.ComplexUnequalTranslatedNormalization
import Langlands.Global.RankinSelberg.ComplexPlaceUnequalFunctionalEquationProof

/-! # Reduction of complex ordinary generation to the standard trace character -/

noncomputable section

open Filter Set
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open ArchimedeanLocal ComplexCharacterChange
open ComplexCompactProfileFamily (characterList)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner)
open ComplexJacquetMultiplicityOne (exists_characterList complexJacquetMultiplicityOne)
open ComplexUnequalTranslatedNormalization (complexUnequalTranslatedNormalization)
open ArchimedeanComplexPairFactor (complexLFactor_ne_zero)

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ

private theorem nonzeroModel_of_leftTranslate {r : ℕ} {S T : Submodule ℂ (G (r + 1) → ℂ)}
    (g : G (r + 1)) (hS : S ≠ ⊥) (hL : ∀ W ∈ S, leftTranslate g W ∈ T) : T ≠ ⊥ := by
  intro hT
  apply hS
  refine le_antisymm (fun W hW => ?_) bot_le
  have hW₀ : leftTranslate g W = 0 := (Submodule.mem_bot ℂ).mp (hT ▸ hL W hW)
  apply (Submodule.mem_bot ℂ).mpr
  funext x
  simpa only [leftTranslate_apply, mul_inv_cancel_left, Pi.zero_apply] using congrFun hW₀ (g⁻¹ * x)

/-- A covering family for the ordinary unequal-rank integral with the standard character
supplies a covering family for the same prescribed parameters at every nonzero trace scale. -/
theorem complexUnequalCoverage_of_standard {r t : ℕ} (h : t < r) {d e : List ComplexCharacterData}
    (hd : d.length = r + 1) (he : e.length = t + 1) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (hGen : HasCoveringOrdinaryNormalizations
      (complexOrdinaryUnequalTest h d e 1 (changeQuotientMeasure a D)) (complexPairLFactor d e)) :
    HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest h d e a D) (complexPairLFactor d e) := by
  intro s₀
  obtain ⟨⟨W, V⟩, Nstd, hNstd⟩ := hGen s₀
  obtain ⟨l, p, rfl⟩ := exists_characterList d hd
  let μ := complexSelfDualMeasure (-a)
  let B := continuedJacquet μ (-a) l p
  have hW : scaleWhittaker a W.val ∈ LinearMap.range B := by
    have hRange : complexWhittakerModel r (characterList l p) a = LinearMap.range B := by
      simpa only [B, neg_neg] using (complexJacquetMultiplicityOne r μ (-a) l p).2
    rw [← hRange]
    exact scaleWhittaker_mem W.2
  obtain ⟨v, hv⟩ := hW
  have hB : IsComplexWhittakerIntertwiner r (characterList l p) a B := by
    simpa only [B, neg_neg] using complexJacquetIntertwiner r μ (-a) l p
  let Vₐ : complexWhittakerModel t e (-a) := ⟨scaleWhittaker a V.val, scaleWhittaker_neg_mem V.2⟩
  let g := unequalScaleCorrection h a
  obtain ⟨U, N, N₀, σ, hN, hRight, hLim, hN₀, _, hRight₀⟩ :=
    complexUnequalTranslatedNormalization r t h (characterList l p) e a D
      (fun Wₐ Xₐ => complexUnequalNormalizedGrowth r t h _ _ List.length_ofFn he a D Wₐ.val Xₐ.val Wₐ.2 Xₐ.2)
      B hB v g Vₐ
  let L := complexPairLFactor (characterList l p) e
  obtain ⟨τ, hτ⟩ := Nstd.eq_on_right
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ s : ℂ, b < s.re → L.denominator s ≠ 0 := complexLFactor_ne_zero _
  have hEq : N₀ = fun s => unequalScaleMultiplier h a s * Nstd.value s := by
    let S := max (max σ τ) b
    have hs : S < ((S + 1 : ℝ) : ℂ).re := by simp
    exact (show AnalyticOnNhd ℂ N₀ univ from fun s _ => hN₀.analyticAt s).eq_of_eventuallyEq
      (((differentiable_unequalScaleMultiplier h a).differentiableOn.analyticOnNhd isOpen_univ).mul Nstd.analytic)
      (z₀ := ((S + 1 : ℝ) : ℂ)) (by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with s hs'
        have hσ : σ < s.re := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hs')
        have hτ' : τ < s.re := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hs')
        have hb' : b < s.re := (le_max_right _ _).trans_lt hs'
        rw [hRight₀ s hσ, hv]
        change L.denominator s * complexUnequalIntegral h D
          (ArchimedeanLocal.translateFunction (unequalScaleCorrection h a) (scaleWhittaker a W.val))
          (scaleWhittaker a V.val) s = _
        rw [unequal_primal_comparison h a D W.2 V.2]
        have hStd : complexUnequalIntegral h (changeQuotientMeasure a D) W.val V.val s =
            Nstd.value s * (L.denominator s)⁻¹ := hτ s hτ'
        rw [hStd]
        field_simp [hb s hb'])
  have hne : N₀ s₀ ≠ 0 := by
    rw [hEq]
    exact mul_ne_zero (unequalScaleMultiplier_ne_zero h a s₀) hNstd
  have hLim₀ : Tendsto (fun n => N n s₀) atTop (𝓝 (N₀ s₀)) :=
    hLim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ s₀)
  have hExists : ∃ n, N n s₀ ≠ 0 := by
    by_contra! hn
    have hz : (fun n => N n s₀) = fun _ => 0 := funext hn
    rw [hz] at hLim₀
    exact hne (tendsto_nhds_unique hLim₀ tendsto_const_nhds)
  obtain ⟨n, hn⟩ := hExists
  refine ⟨(U n, Vₐ), ⟨N n, fun z _ => (hN n).analyticAt z, max σ b, fun s hs => ?_⟩, hn⟩
  change complexUnequalIntegral h D (U n).val Vₐ.val s = N n s * (L.denominator s)⁻¹
  rw [hRight n s ((le_max_left _ _).trans_lt hs), mul_comm (L.denominator s) _, mul_assoc,
    mul_inv_cancel₀ (hb s ((le_max_right _ _).trans_lt hs)), mul_one]

/-- To generate all complex ordinary normalized tests, it suffices to generate pointwise
coverage for standard-character unequal-rank pairs and finite sums for standard-character
equal and adjacent pairs. -/
def ComplexOrdinaryStandardGenerationStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = t + 1 →
    IsIrreducibleGKModule (complexStandardRep (r + 1) d) (complexStandardLie (r + 1) d) →
    IsIrreducibleGKModule (complexStandardRep (t + 1) e) (complexStandardLie (t + 1) e) →
    ∀ D : ComplexQuotientMeasureData t,
      complexWhittakerModel r d 1 ≠ ⊥ → complexWhittakerModel t e (-1) ≠ ⊥ →
      HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest h d e 1 D) (complexPairLFactor d e) ∧
      (t + 1 = r → HasFiniteOrdinaryNormalizationSum
        (complexOrdinaryUnequalTest h d e 1 D) (complexPairLFactor d e))) ∧
  ∀ (r : ℕ) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = r + 1 →
    IsIrreducibleGKModule (complexStandardRep (r + 1) d) (complexStandardLie (r + 1) d) →
    IsIrreducibleGKModule (complexStandardRep (r + 1) e) (complexStandardLie (r + 1) e) →
    ∀ D : ComplexQuotientMeasureData r,
      complexWhittakerModel r d 1 ≠ ⊥ → complexWhittakerModel r e (-1) ≠ ⊥ →
      HasFiniteOrdinaryNormalizationSum (complexOrdinaryEqualTest r d e 1 D) (complexPairLFactor d e)

/-- Standard-character generation suffices for the full published ordinary complex
normalized generation statement. -/
def ComplexOrdinaryStandardGenerationReductionStatement : Prop :=
  ComplexOrdinaryStandardGenerationStatement → ComplexOrdinaryNormalizedGenerationStatement

theorem complexOrdinaryStandardGenerationReduction : ComplexOrdinaryStandardGenerationReductionStatement := by
  rintro ⟨hUnequal, hEqual⟩
  have hnorm (a : ℂˣ) (ha : a = 1 ∨ a = -1) : ‖(a : ℂ)‖ = 1 := by rcases ha with rfl | rfl <;> simp
  constructor
  · intro r t h d e hd he hin hime a D hW hV
    obtain ⟨hCover, hSum⟩ := hUnequal r t h d e hd he hin hime (changeQuotientMeasure a D)
      (nonzeroModel_of_leftTranslate _ hW (fun _ hW₁ => normalizeWhittaker_mem hW₁))
      (nonzeroModel_of_leftTranslate _ hV (fun _ hV₁ => normalizeWhittaker_neg_mem hV₁))
    exact ⟨complexUnequalCoverage_of_standard h hd he a D hCover,
      fun hAdj ha => complexUnequalFiniteSum_scale h a (hnorm a ha) D (hSum hAdj)⟩
  · intro r d e hd he hin hime a D hW hV
    have hSum := hEqual r d e hd he hin hime (changeQuotientMeasure a D)
      (nonzeroModel_of_leftTranslate _ hW (fun _ hW₁ => normalizeWhittaker_mem hW₁))
      (nonzeroModel_of_leftTranslate _ hV (fun _ hV₁ => normalizeWhittaker_neg_mem hV₁))
    exact ⟨complexEqualCoverage_scale a D hSum.covering,
      fun ha => complexEqualFiniteSum_scale a (hnorm a ha) D hSum⟩

end Langlands.Global.RankinSelbergGlobal
