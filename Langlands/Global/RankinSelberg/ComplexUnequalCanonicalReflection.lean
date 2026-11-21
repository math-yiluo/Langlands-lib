import Langlands.Global.RankinSelberg.ComplexPairStripReflection
import Langlands.Global.RankinSelberg.ComplexUnequalCanonicalFamily

/-! # Continuing the normalized unequal-rank equation in the larger exponents -/

noncomputable section

open Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open ArchimedeanLocal
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactProfileFamily (characterList)
open ComplexAdjacentUnfolding (HasComplexPairNormalization complexPairParameterReflection
  complexCentralSign_ne_zero complexPairStripReflection)
open ComplexJacquet (HasComplexPairNormalizedGrowth)

variable {r t : ℕ}
local notation "P" => Fin (r + 1) → ℂ
local notation "L" => Fin (r + 1) → ℤ
local notation "H" => Langlands.GeneralLinear (t + 1) ℂ

/-- The exact pair normalization for every larger canonical Jacquet evaluation at one
inducing parameter and a fixed smaller Whittaker function. -/
def HasUnequalCanonicalPairNormalization (h : t < r) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (D : ComplexQuotientMeasureData t) (l : L) (p : P) (es : List ComplexCharacterData) (V : H → ℂ) : Prop :=
  ∀ f : Automorphic.complexStandardKFinite (r + 1) (characterList l p),
    let W := continuedJacquet μ a l p f
    HasComplexPairNormalization (characterList l p) es (-a) (complexCentralSign es ^ r)
      (complexUnequalIntegral h D W V) (complexUnequalDualIntegral h (-a) D W V)

/-- The normalized equation for a fixed smaller Whittaker vector persists along a holomorphic
family of larger inducing exponents from a small disk about zero to parameter one. -/
def ComplexUnequalCanonicalReflectionStatement : Prop :=
  ∀ (h : t < r) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (l : L) (k : Fin (t + 1) → ℤ) (q : Fin (t + 1) → ℂ) (V : H → ℂ),
    V ∈ complexWhittakerModel t (characterList k q) a →
    ∀ (p : ℂ → P), Differentiable ℂ p →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ,
        HasUnequalCanonicalPairNormalization h μ a D l (p z) (characterList k q) V) →
      HasUnequalCanonicalPairNormalization h μ a D l (p 1) (characterList k q) V

theorem complexUnequalCanonicalReflection :
    ComplexUnequalCanonicalReflectionStatement (r := r) (t := t) := by
  intro h μ a D l k q V hV p hp ⟨δ, hδ, hInit⟩ f
  let es := characterList k q
  let W (z : ℂ) := continuedJacquet μ a l (p z) (transferProfile l (p 1) (p z) f)
  let Z (u : ℂ × ℂ) := complexUnequalIntegral h D (W u.1) V u.2
  let Zd (u : ℂ × ℂ) := complexUnequalDualIntegral h (-a) D (W u.1) V u.2
  let c := complexCentralSign es ^ r
  obtain ⟨σ, _, hZ, hZd⟩ := complexUnequalCanonicalFamily h μ a D l (p 1) f p hp es V hV 3
  have hc : c ≠ 0 := pow_ne_zero _ (complexCentralSign_ne_zero es)
  have hz := complexPairParameterReflection (r + 1) (t + 1) l k p (fun _ => q) (-a) c hc hp
    (differentiable_const q) Z Zd σ hZ hZd
    ⟨δ, hδ, fun z hz => hInit z hz (transferProfile l (p 1) (p z) f)⟩
  simpa only [Z, Zd, W, transferProfile_self] using hz

/-- The pair normalization with exponential strip growth for all larger canonical values. -/
def HasUnequalCanonicalPairGrowth (h : t < r) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (D : ComplexQuotientMeasureData t) (l : L) (p : P) (es : List ComplexCharacterData) (V : H → ℂ) : Prop :=
  ∀ f : Automorphic.complexStandardKFinite (r + 1) (characterList l p),
    let W := continuedJacquet μ a l p f
    HasComplexPairNormalizedGrowth (characterList l p) es (-a) (complexCentralSign es ^ r)
      (complexUnequalIntegral h D W V) (complexUnequalDualIntegral h (-a) D W V)

/-- The growth-preserving continuation of the unequal equation along a holomorphic inducing family. -/
def ComplexUnequalCanonicalGrowthReflectionStatement : Prop :=
  ∀ (h : t < r) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (l : L) (k : Fin (t + 1) → ℤ) (q : Fin (t + 1) → ℂ) (V : H → ℂ),
    V ∈ complexWhittakerModel t (characterList k q) a →
    ∀ (p : ℂ → P), Differentiable ℂ p →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ,
        HasUnequalCanonicalPairGrowth h μ a D l (p z) (characterList k q) V) →
      HasUnequalCanonicalPairGrowth h μ a D l (p 1) (characterList k q) V

theorem complexUnequalCanonicalGrowthReflection :
    ComplexUnequalCanonicalGrowthReflectionStatement (r := r) (t := t) := by
  intro h μ a D l k q V hV p hp ⟨δ, hδ, hInit⟩ f
  let es := characterList k q
  let W (z : ℂ) := continuedJacquet μ a l (p z) (transferProfile l (p 1) (p z) f)
  let Z (u : ℂ × ℂ) := complexUnequalIntegral h D (W u.1) V u.2
  let Zd (u : ℂ × ℂ) := complexUnequalDualIntegral h (-a) D (W u.1) V u.2
  let c := complexCentralSign es ^ r
  obtain ⟨σ, _, hZ, hZd, hBound⟩ := complexUnequalCanonicalFamilyBounds h μ a D l (p 1) f p hp es V hV 3
  have hc : c ≠ 0 := pow_ne_zero _ (complexCentralSign_ne_zero es)
  have hz := complexPairStripReflection (r + 1) (t + 1) l k p (fun _ => q) (-a) c hc hp
    (differentiable_const q) Z Zd σ hZ hZd hBound
    ⟨δ, hδ, fun z hz => hInit z hz (transferProfile l (p 1) (p z) f)⟩
  simpa only [Z, Zd, W, transferProfile_self] using hz

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
