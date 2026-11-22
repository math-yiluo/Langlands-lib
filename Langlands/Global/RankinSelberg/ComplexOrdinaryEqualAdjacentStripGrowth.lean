import Langlands.Global.RankinSelberg.ComplexPlaceEqualFunctionalEquationProof
import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness

/-! # Normalized strip growth of equal and adjacent complex ordinary tests -/

noncomputable section

open Set
open scoped NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal ComplexCharacterChange ComplexJacquet
open Langlands.LocalFactor.Archimedean
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

private theorem stripGrowth_amplitude (a : ℂˣ) (b c : ℝ) :
    HasStripExponentialGrowth (fun s => amplitude a ((b : ℂ) + (c : ℂ) * s)) := by
  apply stripGrowth_of_norm_bounded_on_strips
  intro l u
  let f (x : ℝ) := Real.exp ((b + c * x) * Real.log ‖(a : ℂ)‖)
  have hf : Continuous f := by unfold f; fun_prop
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Icc l u)).image hf).bddAbove
  refine ⟨C, fun s hl hu => ?_⟩
  have h : ‖amplitude a ((b : ℂ) + (c : ℂ) * s)‖ = f s.re := by
    simp [amplitude, f, Complex.norm_exp, Complex.mul_re, Complex.add_re]
  rw [h]
  exact hC ⟨s.re, ⟨hl, hu⟩, rfl⟩

/-- The equal-rank ordinary and dual normalizations have strip growth at any nonzero scale. -/
theorem complexLocalEqualGrowthAtCharacter (r : ℕ) (a : ℂˣ)
    (ds es : List ComplexCharacterData) (hd : ds.length = r + 1) (he : es.length = r + 1)
    (D : ComplexQuotientMeasureData r) (W V : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : 𝓢(Fin (r + 1) → ℂ, ℂ))
    (hW : W ∈ complexWhittakerModel r ds a) (hV : V ∈ complexWhittakerModel r es (-a)) :
    HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
      (complexEqualIntegral D W V Φ) (complexEqualDualIntegral a D W V Φ) := by
  obtain ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨τ, hτ⟩, hE⟩ :=
    complexLocalEqualStandardGrowth r ds es hd he (changeQuotientMeasure a D)
      (normalizeWhittaker a W) (normalizeWhittaker a V) Φ
      (normalizeWhittaker_mem hW) (normalizeWhittaker_neg_mem hV)
  let c := primalMultiplier r a
  let cd := dualMultiplier r ds es a
  have hc : HasStripExponentialGrowth c := by
    convert stripGrowth_amplitude a 0 (-(r : ℝ) * (r + 1)) using 1
    funext s
    unfold c primalMultiplier
    apply congrArg (amplitude a)
    push_cast
    ring
  have hcd : HasStripExponentialGrowth cd := by
    let k := ((centralCharacter ds a : ℂ) * (centralCharacter es a : ℂ)) ^ (r + 1)
    convert (stripGrowth_amplitude a (r + 1) (-(r + 1) * (r + 2))).const_mul k using 1
    funext s
    unfold cd dualMultiplier
    apply congrArg (fun t => k * amplitude a t)
    push_cast
    ring
  refine ⟨fun s => c s * N s, fun s => cd s * Nd s,
    (differentiable_primalMultiplier r a).mul hN, (differentiable_dualMultiplier r ds es a).mul hNd,
    hc.mul hNg, hcd.mul hNdg, ⟨τ, fun s hs => ?_⟩, fun s => ?_⟩
  · constructor
    · change c s * N s = _
      rw [(hτ s hs).1, (primal_comparison hW hV D Φ s).2]
      change c s * _ = _ * (c s * _)
      ring
    · change cd s * Nd s = _
      rw [(hτ s hs).2, (dual_comparison hd he hW hV D Φ s).2]
      change cd s * _ = _ * (cd s * _)
      ring
  · let E : ℂ := complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s
    let E₁ : ℂ := complexPairEpsilon ds es 1 ‖(↑(1 : ℂˣ) : ℂ)‖₊
      (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s
    let sign := complexCentralSign es ^ r
    have heps : E * c s = cd (1 - s) * E₁ := epsilon_mul_primal_eq_dual_mul_standard hd he a s
    change cd (1 - s) * Nd (1 - s) = sign * E * (c s * N s)
    calc
      _ = sign * (cd (1 - s) * E₁) * N s := by rw [hE s]; dsimp only [E₁, sign]; ring
      _ = _ := by rw [← heps]; ring

private theorem ordinaryNormalization_of_pair {ds es : List ComplexCharacterData}
    {a : ℂˣ} {c : ℂ} {I Id : ℂ → ℂ} (h : HasComplexPairNormalizedGrowth ds es a c I Id) :
    ∃ N : OrdinaryIntegralNormalization I (fun s => ((complexPairLFactor ds es).denominator s)⁻¹),
      HasStripExponentialGrowth N.value := by
  obtain ⟨N, _, hN, _, hNg, _, ⟨τ, hτ⟩, _⟩ := h
  obtain ⟨σ, hσ⟩ := complexPairLFactor_denominator_ne_zero ds es
  refine ⟨⟨N, fun s _ => hN.analyticAt s, ⟨max τ σ, fun s hs => ?_⟩⟩, hNg⟩
  rw [(hτ s ((le_max_left _ _).trans_lt hs)).1,
    mul_comm ((complexPairLFactor ds es).denominator s) (I s), mul_assoc,
    mul_inv_cancel₀ (hσ s ((le_max_right _ _).trans_lt hs)), mul_one]

/-- Every equal or adjacent complex ordinary test has an entire normalization, and
each entire normalization has exponential strip growth. -/
def ComplexOrdinaryEqualAdjacentStripGrowthStatement : Prop :=
  (∀ (r : ℕ) (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r),
      HasEntireOrdinaryNormalizations (complexOrdinaryEqualTest r ds es a D)
        (complexPairLFactor ds es) ∧
      HasOrdinaryNormalizationStripGrowth (complexOrdinaryEqualTest r ds es a D)
        (complexPairLFactor ds es)) ∧
  ∀ (r : ℕ) (ds es : List ComplexCharacterData), ds.length = r + 2 → es.length = r + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r),
      HasEntireOrdinaryNormalizations (complexOrdinaryUnequalTest (Nat.lt_succ_self r) ds es a D)
        (complexPairLFactor ds es) ∧
      HasOrdinaryNormalizationStripGrowth (complexOrdinaryUnequalTest (Nat.lt_succ_self r) ds es a D)
        (complexPairLFactor ds es)

theorem complexOrdinaryEqualAdjacentStripGrowth : ComplexOrdinaryEqualAdjacentStripGrowthStatement := by
  constructor
  · intro r ds es hd he a D
    refine ordinaryNormalizationGrowthFromExistence _ _ (complexPairLFactor_denominator_ne_zero ds es) ?_
    rintro ⟨W, V, Φ⟩
    exact ordinaryNormalization_of_pair
      (complexLocalEqualGrowthAtCharacter r a ds es hd he D W V Φ W.2 V.2)
  · intro r ds es hd he a D
    refine ordinaryNormalizationGrowthFromExistence _ _ (complexPairLFactor_denominator_ne_zero ds es) ?_
    rintro ⟨W, V⟩
    exact ordinaryNormalization_of_pair (complexAdjacentFromEqualGrowthAtCharacter r a
      (complexLocalEqualGrowthAtCharacter r a) ds es hd he D W V W.2 V.2)

end Langlands.Global.RankinSelbergGlobal
