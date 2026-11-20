import Langlands.Global.RankinSelberg.RealUniformContinuationReduction
import Langlands.Global.RankinSelberg.ArchimedeanRealPairIdentity

/-!
# The real-place functional equation from Jacquet's pair identity

See the paired Markdown file.
-/

noncomputable section

universe u

open MeasureTheory
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal ArchimedeanRealPairIdentity

local instance realUPairIdGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realUPairIdGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realUPairIdNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realUPairIdNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realUPairIdQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance realUPairIdQBorel (n : ℕ) :
    BorelSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- Unequal-rank pair-identity premise on the uniform coefficient space: the data of
`RealLocalUniformUnequalContinuationStatement`, with Jacquet's pair identity in place of the
continuation part. -/
def RealLocalUniformUnequalPairIdentityStatement : Prop := by
  classical
  exact
  ∀ (r t : ℕ) (h : t < r) (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = t + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel t es (-a) →
    UnequalPairIdentity h a D W W' ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) (-a)
      ((RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) *
        (RealJacquet.determinant es (-1) : ℂ))

/-- Positive equal-rank pair-identity premise on the uniform coefficient space: the data of
`RealLocalUniformPositiveEqualContinuationStatement`, with Jacquet's pair identity in place of
the continuation part. -/
def RealLocalUniformPositiveEqualPairIdentityStatement : Prop := by
  classical
  exact
  ∀ (r : ℕ), 0 < r → ∀ (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = r + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel r es (-a) →
    EqualPairIdentity a (-a) D W W' Φ ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock)
      ((RealJacquet.determinant ds (-1) : ℂ) ^ r)

/-- The unequal-rank continuation premise follows from the pair identity. -/
theorem realLocalUniformUnequalContinuation_of_pairIdentity
    (hP : RealLocalUniformUnequalPairIdentityStatement) :
    RealLocalUniformUnequalContinuationStatement := by
  intro r t h ds es hds hes a D W W' hW hW'
  have hR := realUniformWhittakerRegularity r ds a W hW
  have hR' := realUniformWhittakerRegularity t es (-a) W' hW'
  obtain ⟨σ₀, hK, hKd, -, -⟩ :=
    realUnequalPairConvergence r t h D a W W' hR.1 hR.2 hR'.1 hR'.2
  exact realPairIdentityContinuation.1 r t h a (-a) D W W' ds es _ _ _ σ₀
    (mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (Units.ne_zero _)) hK hKd
    (hP r t h ds es hds hes a D W W' hW hW')

/-- The positive equal-rank continuation premise follows from the pair identity. -/
theorem realLocalUniformPositiveEqualContinuation_of_pairIdentity
    (hP : RealLocalUniformPositiveEqualPairIdentityStatement) :
    RealLocalUniformPositiveEqualContinuationStatement := by
  intro r hr ds es hds hes a D W W' Φ hW hW'
  have hR := realUniformWhittakerRegularity r ds a W hW
  have hR' := realUniformWhittakerRegularity r es (-a) W' hW'
  obtain ⟨σ₀, hK, hKd, -, -⟩ :=
    realEqualPairConvergence r D a (-a) W W' Φ hR.1 hR.2 hR'.1 hR'.2
  exact realPairIdentityContinuation.2 r a (-a) D W W' Φ ds es _ _ _ σ₀
    (pow_ne_zero _ (Units.ne_zero _)) hK hKd (hP r hr ds es hds hes a D W W' Φ hW hW')

/-- The real-place functional equation from Jacquet's pair identity in both ranks on the
uniform coefficient spaces and the contragredient pair-denominator premise. -/
def RealPlacePairIdentityReductionStatement : Prop :=
  RealLocalUniformUnequalPairIdentityStatement →
    RealLocalUniformPositiveEqualPairIdentityStatement →
    RealPlaceContragredientPairLStatement.{u} → RealPlaceFunctionalEquationStatement.{u}

theorem realPlacePairIdentityReduction : RealPlacePairIdentityReductionStatement.{u} :=
  fun hU hE hD => realPlaceUniformContinuationReduction.{u}
    (realLocalUniformUnequalContinuation_of_pairIdentity hU)
    (realLocalUniformPositiveEqualContinuation_of_pairIdentity hE) hD

end Langlands.Global.RankinSelbergGlobal
