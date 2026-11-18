import Langlands.Global.RankinSelberg.ComplexLocalDualWhittaker
import Langlands.Global.RankinSelberg.ComplexLocalFourierSchwartz

/-! # Dual analytic clauses from the primal complex equal-rank integrals -/

noncomputable section

open MeasureTheory Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- Convergence, holomorphy and meromorphic continuation of the original complex equal-rank
integral for all inducing lists and model vectors. -/
def ComplexLocalEqualPrimalAnalyticStatement : Prop :=
  ∀ (r : ℕ) (d d' : List ComplexCharacterData), d.length = r + 1 → d'.length = r + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
    W ∈ complexWhittakerModel r d a → W' ∈ complexWhittakerModel r d' (-a) →
  ∃ (σ : ℝ) (M : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
    DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧
    (∀ s : ℂ, σ < s.re → complexEqualIntegral D W W' Φ s = M s)

/-- The complex equal-rank functional equation for supplied continuations that agree with
the integrals on a common right half-plane. -/
def ComplexLocalEqualMeromorphicEquationStatement : Prop :=
  ∀ (r : ℕ) (d d' : List ComplexCharacterData), d.length = r + 1 → d'.length = r + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
    W ∈ complexWhittakerModel r d a → W' ∈ complexWhittakerModel r d' (-a) →
  ∀ (σ : ℝ) (M Md : ℂ → ℂ), MeromorphicOn M Set.univ → MeromorphicOn Md Set.univ →
    (∀ s : ℂ, σ < s.re → complexEqualIntegral D W W' Φ s = M s) →
    (∀ s : ℂ, σ < s.re → complexEqualDualIntegral a D W W' Φ s = Md s) →
    ∀ᶠ s in Filter.codiscrete ℂ,
      ((complexPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
        complexCentralSign d' ^ r *
          (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
          ((complexPairLFactor (d.map ComplexCharacterData.inv)
            (d'.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹ * M s

/-- The primal analytic clauses and the identity for agreeing continuations suffice for the
exact complex equal-rank local statement. -/
def ComplexLocalEqualDualityReductionStatement : Prop :=
  ComplexLocalEqualPrimalAnalyticStatement →
    ComplexLocalEqualMeromorphicEquationStatement →
      ComplexLocalEqualFunctionalEquationStatement

theorem complexLocalEqualDualityReduction : ComplexLocalEqualDualityReductionStatement := by
  intro hAnalytic hEquation r d d' hd hd' a D W W' Φ hW hW'
  obtain ⟨σ, M, hInt, hHol, hM, hEq⟩ := hAnalytic r d d' hd hd' a D W W' Φ hW hW'
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_complexFourierTransform a Φ
  let dDual := d.reverse.map ComplexCharacterData.inv
  let d'Dual := d'.reverse.map ComplexCharacterData.inv
  have hdDual : dDual.length = r + 1 := by simpa [dDual] using hd
  have hd'Dual : d'Dual.length = r + 1 := by simpa [d'Dual] using hd'
  let Wd := ArchimedeanLocal.dualFunction (r + 1) W
  let W'd := ArchimedeanLocal.dualFunction (r + 1) W'
  have hWd : Wd ∈ complexWhittakerModel r dDual (-a) :=
    complexLocalDualWhittaker_mem hd hW
  have hW'd : W'd ∈ complexWhittakerModel r d'Dual (-(-a)) :=
    complexLocalDualWhittaker_mem hd' hW'
  obtain ⟨σd, Md, hIntd, hHold, hMd, hEqd⟩ :=
    hAnalytic r dDual d'Dual hdDual hd'Dual (-a) D Wd W'd Ψ hWd hW'd
  let σ₀ := max σ σd
  have hσ {s : ℂ} (hs : σ₀ < s.re) : σ < s.re := (le_max_left σ σd).trans_lt hs
  have hσd {s : ℂ} (hs : σ₀ < s.re) : σd < s.re := (le_max_right σ σd).trans_lt hs
  have hDualIntegral : complexEqualDualIntegral a D W W' Φ = complexEqualIntegral D Wd W'd Ψ := by
    rw [hΨ]
    rfl
  have hEq₀ (s : ℂ) (hs : σ₀ < s.re) : complexEqualIntegral D W W' Φ s = M s :=
    hEq s (hσ hs)
  have hEqd₀ (s : ℂ) (hs : σ₀ < s.re) : complexEqualDualIntegral a D W W' Φ s = Md s := by
    rw [hDualIntegral]
    exact hEqd s (hσd hs)
  refine ⟨σ₀, M, Md, fun s hs => hInt s (hσ hs), ?_, hHol.mono (fun _ => hσ), ?_,
    hM, hMd, hEq₀, hEqd₀, hEquation r d d' hd hd' a D W W' Φ hW hW' σ₀ M Md hM hMd hEq₀ hEqd₀⟩
  · intro s hs
    rw [← hΨ]
    exact hIntd s (hσd hs)
  · rw [hDualIntegral]
    exact hHold.mono (fun _ => hσd)

end Langlands.Global.RankinSelbergGlobal
