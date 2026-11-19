import Langlands.Global.RankinSelberg.RealUnequalPairConvergence
import Langlands.Global.RankinSelberg.RealUniformLocalTheoryReduction

/-! # The uniform real local equations from continuation premises

The convergence and holomorphy conjuncts of the uniform local packages are proved; only the
meromorphic continuation and the functional equation remain as premises. -/

noncomputable section
universe u
open MeasureTheory
open Langlands.LocalFactor.Archimedean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

namespace RealJacquet

/-- The last five conjuncts of `EquationPackage`: meromorphic continuations of the two
integral functions, agreement on a right half-plane, and the multiplied-out functional
equation off a discrete set. -/
def ContinuationPackage (Z Zd L Ld E : ℂ → ℂ) (sign : ℂ) : Prop :=
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → Z s = M s) ∧
    (∀ s : ℂ, σ < s.re → Zd s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      L s * Md (1 - s) = sign * E s * Ld (1 - s) * M s

/-- An equation package yields its continuation part. -/
theorem EquationPackage.continuation
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {K : ℂ → X → ℂ} {Kd : ℂ → Y → ℂ}
    {Z Zd L Ld E : ℂ → ℂ} {sign : ℂ}
    (h : EquationPackage μ ν K Kd Z Zd L Ld E sign) :
    ContinuationPackage Z Zd L Ld E sign := by
  obtain ⟨σ, M, Md, -, -, -, -, hM, hMd, hZM, hZdMd, hFE⟩ := h
  exact ⟨σ, M, Md, hM, hMd, hZM, hZdMd, hFE⟩

/-- Convergence and holomorphy on one right half-plane together with the continuation part
give the full equation package, on the intersection of the two half-planes. -/
theorem equationPackage_of_continuation
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {K : ℂ → X → ℂ} {Kd : ℂ → Y → ℂ}
    {Z Zd L Ld E : ℂ → ℂ} {sign : ℂ}
    (hconv : ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (K s) μ) ∧
      (∀ s : ℂ, σ < s.re → Integrable (Kd s) ν) ∧
      DifferentiableOn ℂ Z {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ Zd {s : ℂ | σ < s.re})
    (hcont : ContinuationPackage Z Zd L Ld E sign) :
    EquationPackage μ ν K Kd Z Zd L Ld E sign := by
  obtain ⟨σ₁, hK, hKd, hZ, hZd⟩ := hconv
  obtain ⟨σ₂, M, Md, hM, hMd, hZM, hZdMd, hFE⟩ := hcont
  have h₁ : ∀ s : ℂ, max σ₁ σ₂ < s.re → σ₁ < s.re :=
    fun s hs => lt_of_le_of_lt (le_max_left _ _) hs
  have h₂ : ∀ s : ℂ, max σ₁ σ₂ < s.re → σ₂ < s.re :=
    fun s hs => lt_of_le_of_lt (le_max_right _ _) hs
  exact ⟨max σ₁ σ₂, M, Md, fun s hs => hK s (h₁ s hs), fun s hs => hKd s (h₁ s hs),
    hZ.mono fun s hs => h₁ s hs, hZd.mono fun s hs => h₁ s hs, hM, hMd,
    fun s hs => hZM s (h₂ s hs), fun s hs => hZdMd s (h₂ s hs), hFE⟩

/-- The continuation part of `UnequalEquation`, with the same arguments. -/
def UnequalContinuation {r t : ℕ} (h : t < r) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (ds es dds ees : List RealBlock) (b : ℝˣ) (sign : ℂ) : Prop :=
  ContinuationPackage
    (realUnequalIntegral h D W W') (realUnequalDualIntegral h a D W W')
    (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
    (fun s => ((realPairLFactor dds ees).denominator s)⁻¹)
    (fun s => (realPairEpsilon ds es b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ)) sign

/-- The continuation part of `EqualEquation`, with the same arguments. -/
def EqualContinuation {r : ℕ} (a b : ℝˣ) (D : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (ds es dds ees : List RealBlock) (sign : ℂ) : Prop :=
  ContinuationPackage
    (realEqualIntegral D W W' Φ) (realEqualDualIntegral b D W W' Φ)
    (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
    (fun s => ((realPairLFactor dds ees).denominator s)⁻¹)
    (fun s => (realPairEpsilon ds es b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ)) sign

end RealJacquet

local instance realUContGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realUContGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realUContNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realUContNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realUContQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance realUContQBorel (n : ℕ) :
    BorelSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- Unequal-rank continuation premise on the uniform coefficient space: the data of
`RealLocalUniformUnequalJacquetStatement`, with only the continuation part of the package. -/
def RealLocalUniformUnequalContinuationStatement : Prop := by
  classical
  exact
  ∀ (r t : ℕ) (h : t < r) (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = t + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel t es (-a) →
    RealJacquet.UnequalContinuation h a D W W' ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) (-a)
      ((RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) *
        (RealJacquet.determinant es (-1) : ℂ))

/-- Positive equal-rank continuation premise on the uniform coefficient space: the data of
`RealLocalUniformPositiveEqualJacquetStatement`, with only the continuation part. -/
def RealLocalUniformPositiveEqualContinuationStatement : Prop := by
  classical
  exact
  ∀ (r : ℕ), 0 < r → ∀ (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = r + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel r es (-a) →
    RealJacquet.EqualContinuation a (-a) D W W' Φ ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock)
      ((RealJacquet.determinant ds (-1) : ℂ) ^ r)

/-- The unequal-rank uniform local package follows from its continuation part. -/
theorem realLocalUniformUnequalJacquet_of_continuation
    (hC : RealLocalUniformUnequalContinuationStatement) :
    RealLocalUniformUnequalJacquetStatement := by
  intro r t h ds es hds hes a D W W' hW hW'
  have hR := realUniformWhittakerRegularity r ds a W hW
  have hR' := realUniformWhittakerRegularity t es (-a) W' hW'
  exact RealJacquet.equationPackage_of_continuation
    (realUnequalPairConvergence r t h D a W W' hR.1 hR.2 hR'.1 hR'.2)
    (hC r t h ds es hds hes a D W W' hW hW')

/-- The positive equal-rank uniform local package follows from its continuation part. -/
theorem realLocalUniformPositiveEqualJacquet_of_continuation
    (hC : RealLocalUniformPositiveEqualContinuationStatement) :
    RealLocalUniformPositiveEqualJacquetStatement := by
  intro r hr ds es hds hes a D W W' Φ hW hW'
  have hR := realUniformWhittakerRegularity r ds a W hW
  have hR' := realUniformWhittakerRegularity r es (-a) W' hW'
  exact RealJacquet.equationPackage_of_continuation
    (realEqualPairConvergence r D a (-a) W W' Φ hR.1 hR.2 hR'.1 hR'.2)
    (hC r hr ds es hds hes a D W W' Φ hW hW')

/-- The real-place functional equation from the two continuation premises and the
contragredient pair-denominator premise. -/
def RealPlaceUniformContinuationReductionStatement : Prop :=
  RealLocalUniformUnequalContinuationStatement →
    RealLocalUniformPositiveEqualContinuationStatement →
    RealPlaceContragredientPairLStatement.{u} → RealPlaceFunctionalEquationStatement.{u}

theorem realPlaceUniformContinuationReduction :
    RealPlaceUniformContinuationReductionStatement.{u} :=
  fun hU hE hD => realPlaceUniformLocalTheoryReduction.{u}
    (realLocalUniformUnequalJacquet_of_continuation hU)
    (realLocalUniformPositiveEqualJacquet_of_continuation hE) hD

end Langlands.Global.RankinSelbergGlobal
