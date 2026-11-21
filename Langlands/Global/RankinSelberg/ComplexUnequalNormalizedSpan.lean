import Langlands.Global.RankinSelberg.ComplexAdjacentNormalizedProducts
import Langlands.Global.RankinSelberg.ComplexUnequalAnalyticReduction

/-! # The normalized unequal-rank equation is preserved by linear spanning -/

noncomputable section

open MeasureTheory
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open ComplexJacquet (HasComplexPairNormalizedGrowth)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable
  archimedeanComplexQBorel

/-- Fixing the second function, the first functions with convergence and normalized
functional equation form a submodule. -/
def complexUnequalNormalizedSpace {r t : ℕ} (h : t < r) (D : ComplexQuotientMeasureData t)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ) :
    Submodule ℂ (Langlands.GeneralLinear (r + 1) ℂ → ℂ) :=
  (normalizedKernelPairs D.measure (complexUnequalDualMeasure (r := r) a D)
    (complexPairLFactor ds es).denominator
    (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator
    (fun s => complexCentralSign es ^ r *
      (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ))).comap
        ((complexUnequalKernelPair h).flip V)

/-- Membership in the normalized subspace is precisely joint convergence and the
normalization of the ordinary and dual integrals named in the unequal-rank statement. -/
def ComplexUnequalNormalizedSpanStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ),
    W ∈ complexUnequalNormalizedSpace h D ds es a V ↔
      (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexUnequalIntegrand h W V s) D.measure ∧
        Integrable (complexUnequalDualKernel h W V s) (complexUnequalDualMeasure (r := r) a D)) ∧
      HasComplexPairNormalization ds es a (complexCentralSign es ^ r)
        (complexUnequalIntegral h D W V) (complexUnequalDualIntegral h a D W V)

theorem complexUnequalNormalizedSpan : ComplexUnequalNormalizedSpanStatement := by
  intro r t h D ds es a W V
  constructor
  · rintro ⟨σ, N, Nd, hN, hNd, hright, hEq⟩
    refine ⟨⟨σ, fun s hs => ⟨(hright s hs).1, (hright s hs).2.1⟩⟩,
      ⟨N, Nd, hN, hNd, ⟨σ, ?_⟩, hEq⟩⟩
    intro s hs
    have hs' := hright s hs
    refine ⟨hs'.2.2.1, ?_⟩
    rw [complexUnequalDualIntegral_eq_prod h a D W V s hs'.2.1]
    exact hs'.2.2.2
  · rintro ⟨⟨σ, hσ⟩, N, Nd, hN, hNd, ⟨τ, hτ⟩, hEq⟩
    refine ⟨max σ τ, N, Nd, hN, hNd, ?_, hEq⟩
    intro s hs
    obtain ⟨hI, hId⟩ := hσ s ((le_max_left _ _).trans_lt hs)
    obtain ⟨hL, hLd⟩ := hτ s ((le_max_right _ _).trans_lt hs)
    refine ⟨hI, hId, hL, ?_⟩
    rw [complexUnequalDualIntegral_eq_prod h a D W V s hId] at hLd
    exact hLd

private def normalizedGrowthKernelPairs {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (L Ld E : ℂ → ℂ) :
    Submodule ℂ ((ℂ → X → ℂ) × (ℂ → Y → ℂ)) where
  carrier := {K | ∃ (σ : ℝ) (N Nd : ℂ → ℂ),
    Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
    HasStripExponentialGrowth N ∧ HasStripExponentialGrowth Nd ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (K.1 s) μ ∧ Integrable (K.2 s) ν ∧
      N s = L s * (∫ x, K.1 s x ∂μ) ∧ Nd s = Ld s * (∫ y, K.2 s y ∂ν)) ∧
    ∀ s : ℂ, Nd (1 - s) = E s * N s}
  zero_mem' := by
    refine ⟨0, 0, 0, differentiable_const 0, differentiable_const 0,
      HasStripExponentialGrowth.const 0, HasStripExponentialGrowth.const 0, ?_, ?_⟩ <;> simp
  add_mem' := by
    rintro K P ⟨σK, NK, NKd, hNK, hNKd, hNKg, hNKdg, hK, hKE⟩ ⟨σP, NP, NPd, hNP, hNPd, hNPg, hNPdg, hP, hPE⟩
    refine ⟨max σK σP, NK + NP, NKd + NPd, hNK.add hNP, hNKd.add hNPd,
      hNKg.add hNPg, hNKdg.add hNPdg, ?_, ?_⟩
    · intro s hs
      obtain ⟨hK₁, hK₂, hK₃, hK₄⟩ := hK s ((le_max_left _ _).trans_lt hs)
      obtain ⟨hP₁, hP₂, hP₃, hP₄⟩ := hP s ((le_max_right _ _).trans_lt hs)
      refine ⟨hK₁.add hP₁, hK₂.add hP₂, ?_, ?_⟩
      · simp only [Prod.fst_add, Pi.add_apply, hK₃, hP₃, integral_add hK₁ hP₁, mul_add]
      · simp only [Prod.snd_add, Pi.add_apply, hK₄, hP₄, integral_add hK₂ hP₂, mul_add]
    · intro s
      simp only [Pi.add_apply, hKE s, hPE s, mul_add]
  smul_mem' := by
    rintro c K ⟨σ, N, Nd, hN, hNd, hNg, hNdg, hK, hE⟩
    refine ⟨σ, c • N, c • Nd, hN.const_mul c, hNd.const_mul c,
      hNg.const_mul c, hNdg.const_mul c, ?_, ?_⟩
    · intro s hs
      obtain ⟨hK₁, hK₂, hK₃, hK₄⟩ := hK s hs
      refine ⟨hK₁.const_mul c, hK₂.const_mul c, ?_, ?_⟩
      · change c * N s = L s * (∫ x, c * K.1 s x ∂μ)
        rw [hK₃, integral_const_mul]
        ring
      · change c * Nd s = Ld s * (∫ y, c * K.2 s y ∂ν)
        rw [hK₄, integral_const_mul]
        ring
    · intro s
      simp only [Pi.smul_apply, smul_eq_mul, hE s]
      ring

/-- Fixing the second function, convergence and the normalized equation with exponential
strip growth define a submodule of the first functions. -/
def complexUnequalNormalizedGrowthSpace {r t : ℕ} (h : t < r) (D : ComplexQuotientMeasureData t)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ) :
    Submodule ℂ (Langlands.GeneralLinear (r + 1) ℂ → ℂ) :=
  (normalizedGrowthKernelPairs D.measure (complexUnequalDualMeasure (r := r) a D)
    (complexPairLFactor ds es).denominator
    (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator
    (fun s => complexCentralSign es ^ r *
      (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ))).comap
        ((complexUnequalKernelPair h).flip V)

/-- The growth-preserving subspace gives joint convergence and the normalized equation
with strip growth for the exact ordinary and dual unequal-rank integrals. -/
def ComplexUnequalNormalizedGrowthSpanStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ),
    W ∈ complexUnequalNormalizedGrowthSpace h D ds es a V ↔
      (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexUnequalIntegrand h W V s) D.measure ∧
        Integrable (complexUnequalDualKernel h W V s) (complexUnequalDualMeasure (r := r) a D)) ∧
      HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
        (complexUnequalIntegral h D W V) (complexUnequalDualIntegral h a D W V)

theorem complexUnequalNormalizedGrowthSpan : ComplexUnequalNormalizedGrowthSpanStatement := by
  intro r t h D ds es a W V
  constructor
  · rintro ⟨σ, N, Nd, hN, hNd, hNg, hNdg, hright, hEq⟩
    refine ⟨⟨σ, fun s hs => ⟨(hright s hs).1, (hright s hs).2.1⟩⟩,
      ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨σ, ?_⟩, hEq⟩⟩
    intro s hs
    have hs' := hright s hs
    refine ⟨hs'.2.2.1, ?_⟩
    rw [complexUnequalDualIntegral_eq_prod h a D W V s hs'.2.1]
    exact hs'.2.2.2
  · rintro ⟨⟨σ, hσ⟩, N, Nd, hN, hNd, hNg, hNdg, ⟨τ, hτ⟩, hEq⟩
    refine ⟨max σ τ, N, Nd, hN, hNd, hNg, hNdg, ?_, hEq⟩
    intro s hs
    obtain ⟨hI, hId⟩ := hσ s ((le_max_left _ _).trans_lt hs)
    obtain ⟨hL, hLd⟩ := hτ s ((le_max_right _ _).trans_lt hs)
    refine ⟨hI, hId, hL, ?_⟩
    rw [complexUnequalDualIntegral_eq_prod h a D W V s hId] at hLd
    exact hLd

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
