import Langlands.Global.RankinSelberg.EqualWhittakerPositiveRankReduction
import Langlands.Global.RankinSelberg.ArchimedeanDualNonvanishing
import Langlands.Global.RankinSelberg.RealPlaceEqualPairConvergence
import Langlands.Global.RankinSelberg.ComplexEqualPairConvergence
import Langlands.Global.RankinSelberg.UnequalPlaceTestsFromOrdinary
import Langlands.Global.RankinSelberg.UnequalInfiniteWhittakerSliceReduction
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationProof
import Langlands.Global.RankinSelberg.RectangleTateProof
import Langlands.Global.RankinSelberg.UnipotentClassProductProof

/-! # The factorization over `S` and the infinite places from ordinary archimedean tests

Cogdell 2004, proof of Theorem 4.1, pp.219-220. `ArchimedeanFactorizationStatement` follows
from the archimedean Whittaker slice comparison `InfiniteWhittakerSliceModelStatement`, the
real-place functional equation `RealPlaceFunctionalEquationStatement`, and four assertions of
ordinary nonvanishing on actual archimedean restrictions: the published unequal-rank
`RealUnequalOrdinaryPlaceTestsStatement` and `ComplexUnequalOrdinaryPlaceTestsStatement`, and
their equal-rank analogues in ranks `GL_(r+1)`, `0 < r`, stated here. The dual nonvanishing
clauses are derived from the local functional equations; at the complex places these are the
proved `complexPlaceFunctionalEquation`. See the paired Markdown.
-/

noncomputable section
open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic Langlands.LocalFactor.Archimedean ArchimedeanLocal
open Langlands.Global.HeckeFunctionalEquation

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanComplexGLMeasurable
  archimedeanComplexGLBorel archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

/-- Ordinary nonvanishing at a real place for groups `GL_(r+1)` with `0 < r`: one pair of
actual restrictions, a Schwartz function on the last-row space and quotient measure data whose
ordinary equal-rank integral is nonzero at points arbitrarily far to the right. -/
def RealEqualOrdinaryPlaceTestsPositiveRankStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ), 0 < r →
  ∀ (T T' : CuspidalOperatorRealization F r) (v : RP F) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' : List RealBlock),
    T.realization.HasRealPlaceParameter v d → T'.realization.HasRealPlaceParameter v d' →
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ) (D : RealQuotientMeasureData r),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ realEqualIntegral D W W' Φ s ≠ 0

/-- Ordinary nonvanishing at a complex place for groups `GL_(r+1)` with `0 < r`. -/
def ComplexEqualOrdinaryPlaceTestsPositiveRankStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ), 0 < r →
  ∀ (T T' : CuspidalOperatorRealization F r) (w : CP F) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d d' : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter w d → T'.realization.HasComplexPlaceParameter w d' →
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ) (D : ComplexQuotientMeasureData r),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ complexEqualIntegral D W W' Φ s ≠ 0

/-- A function holomorphic on a right half-plane and nonzero at points arbitrarily far to the
right is holomorphic and nonzero somewhere on that half-plane. -/
theorem holomorphicNonzeroOnRightHalfPlane_of_frequently {f : ℂ → ℂ} {σ : ℝ}
    (hd : DifferentiableOn ℂ f {s : ℂ | σ < s.re})
    (hn : ∀ τ : ℝ, ∃ s : ℂ, τ < s.re ∧ f s ≠ 0) : HolomorphicNonzeroOnRightHalfPlane f := by
  obtain ⟨z, hz, hne⟩ := hn σ
  exact ⟨σ, hd, z, hz, hne⟩

/-- The real equal-rank place tests in positive rank follow from ordinary nonvanishing and the
real equal-rank functional equation, which carries the nonvanishing to the dual integral of
the same test. -/
theorem realEqualPlaceTestsPositiveRank_of_ordinary
    (hFE : RealEqualFunctionalEquationStatement.{u})
    (hOrd : RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u}) :
    RealEqualPlaceTestsPositiveRankStatement.{u} := by
  intro F _ _ _ ψ hψ r hr T Td T' Td' hTd hTd' v a ha d d' dd dd' hd hd' hdd hdd'
  obtain ⟨W, W', Φ, D, hW, hW', hn⟩ := hOrd F ψ hψ r hr T T' v a ha d d' hd hd'
  obtain ⟨σ, -, -, hdiff, -⟩ := realPlaceEqualPairConvergence ψ hψ T T' v a ha hd hd' D Φ hW hW'
  have h₀ : HolomorphicNonzeroOnRightHalfPlane (realEqualIntegral D W W' Φ) :=
    holomorphicNonzeroOnRightHalfPlane_of_frequently hdiff hn
  exact ⟨W, W', Φ, D, hW, hW', h₀, realEqualDualNonvanishing_of_equation ψ hψ T Td T' Td' hTd hTd'
    hFE v a ha d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW' h₀⟩

/-- The complex equal-rank place tests in positive rank follow from ordinary nonvanishing; the
dual nonvanishing comes from the proved complex-place functional equation. -/
theorem complexEqualPlaceTestsPositiveRank_of_ordinary
    (hOrd : ComplexEqualOrdinaryPlaceTestsPositiveRankStatement.{u}) :
    ComplexEqualPlaceTestsPositiveRankStatement.{u} := by
  intro F _ _ _ ψ hψ r hr T Td T' Td' hTd hTd' w a ha d d' dd dd' hd hd' hdd hdd'
  obtain ⟨W, W', Φ, D, hW, hW', hn⟩ := hOrd F ψ hψ r hr T T' w a ha d d' hd hd'
  obtain ⟨σ, -, -, hdiff, -⟩ :=
    complexPlaceEqualPairConvergence ψ hψ T T' w a ha hd hd' D Φ hW hW'
  have h₀ : HolomorphicNonzeroOnRightHalfPlane (complexEqualIntegral D W W' Φ) :=
    holomorphicNonzeroOnRightHalfPlane_of_frequently hdiff hn
  exact ⟨W, W', Φ, D, hW, hW', h₀, complexEqualDualNonvanishing_of_equation ψ hψ T Td T' Td'
    hTd hTd' complexPlaceFunctionalEquation.2 w a ha d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
    h₀⟩

/-- The slice comparison in every rank contains its positive-rank case. -/
theorem infiniteWhittakerSliceModelPositiveRank_of_all
    (h : InfiniteWhittakerSliceModelStatement.{u, uQ}) :
    InfiniteWhittakerSliceModelPositiveRankStatement.{u, uQ} :=
  fun F _ _ _ r _ => h F r

/-- **Conditional factorization from ordinary archimedean tests.** The slice comparison, the
real-place functional equation and the four ordinary nonvanishing assertions at real and
complex places, unequal and equal ranks, imply `ArchimedeanFactorizationStatement`. -/
def ArchimedeanFactorizationOrdinaryReductionStatement : Prop :=
  InfiniteWhittakerSliceModelStatement.{u, uQ} → RealPlaceFunctionalEquationStatement.{u} →
    RealUnequalOrdinaryPlaceTestsStatement.{u} → ComplexUnequalOrdinaryPlaceTestsStatement.{u} →
    RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u} →
    ComplexEqualOrdinaryPlaceTestsPositiveRankStatement.{u} →
    ArchimedeanFactorizationStatement.{u, uQ}

/-- Proof of the conditional factorization. Unequal ranks: the published slice reduction gives
the pointwise premise from the place tests, which come from ordinary nonvanishing and the local
functional equations; the pointwise premise is integrated with the proved measure premises.
Equal ranks: the positive-rank reduction applied to the place tests obtained above. -/
theorem archimedeanFactorizationOrdinaryReduction :
    ArchimedeanFactorizationOrdinaryReductionStatement.{u, uQ} :=
  fun hSlice hRealFE hRU hCU hRE hCE =>
    ⟨unequalArchimedeanFactorizationReduction
        (unequalInfiniteWhittakerSliceReduction hSlice
          (realUnequalPlaceTests_of_ordinary hRealFE.1 hRU)
          (complexUnequalPlaceTests_of_ordinary complexPlaceFunctionalEquation.1 hCU))
        UnipotentClass.unipotentClassProductStatement RectangleTate.rectangleTateStatement,
      equalWhittakerPositiveRankReduction (infiniteWhittakerSliceModelPositiveRank_of_all hSlice)
        (realEqualPlaceTestsPositiveRank_of_ordinary hRealFE.2 hRE)
        (complexEqualPlaceTestsPositiveRank_of_ordinary hCE)⟩

end Langlands.Global.RankinSelbergGlobal
