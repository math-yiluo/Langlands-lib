import Langlands.Global.RankinSelberg.ComplexOrdinaryEqualCoverage
import Langlands.Global.RankinSelberg.ComplexOrdinaryEqualPolynomial
import Langlands.Global.RankinSelberg.ComplexUnequalSpectralMultiplication

/-! # Finite normalized ordinary sums in equal and adjacent complex ranks -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.Archimedean Langlands.LocalFactor.Archimedean
open ComplexEqualPolynomialGeneration (complexEqualFiniteSumFromPolynomials)
open ComplexUnequalSpectralMultiplication (complexUnequalFiniteSumFromPolynomials)

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem adjacentCoverage_of_equalCoverage (r : ℕ) (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1)
    (h : ComplexEqualGaussianCoverageAtRank r a) : ComplexAdjacentCoverageAtRank r a := by
  intro ds es hd he hId hIe D
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < ds.length)
  have hds : ds.length = r + 1 := by simpa only [List.length_cons, Nat.succ_inj] using hd
  have hI := complexStandardIrreducible_of_sublist hd (List.sublist_cons_self d ds) hId
  rw [hds] at hI
  have ha' : ‖((-a : ℂˣ) : ℂ)‖ = 1 := by simpa only [Units.val_neg, norm_neg] using ha
  have hCov := complexOrdinaryAdjacentCoverageStep r (-a) ha' d ds es hds he hId hIe D
    (by rw [neg_neg]; exact h ds es hds he hI hIe D)
  rw [neg_neg] at hCov
  exact hCov

/-- At unit absolute value of the complex trace scale, ordinary adjacent tests and equal-rank
standard Gaussian row tests cover every spectral point for irreducible supplied lists. -/
def ComplexOrdinaryEqualAdjacentCoverageStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ), ‖(a : ℂ)‖ = 1 →
    ComplexEqualGaussianCoverageAtRank r a ∧ ComplexAdjacentCoverageAtRank r a

theorem complexOrdinaryEqualAdjacentCoverage : ComplexOrdinaryEqualAdjacentCoverageStatement := by
  have hEq (r : ℕ) : ∀ a : ℂˣ, ‖(a : ℂ)‖ = 1 → ComplexEqualGaussianCoverageAtRank r a := by
    induction r with
    | zero =>
      intro a _ ds es hd he _ _ D s
      obtain ⟨i, N, hN⟩ := (ComplexRankZero.complexRankZeroGaussianGeneration ds es hd he a D).2
        (complexWhittakerModel_ne_bot_of_length ds hd a) (complexWhittakerModel_ne_bot_of_length es he (-a))
      exact ⟨i, N, by rw [hN]; exact one_ne_zero⟩
    | succ r ih =>
      intro a ha ds es hd he hId hIe D
      obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < ds.length)
      have hds : ds.length = r + 1 := by simpa only [List.length_cons, Nat.succ_inj] using hd
      have ha' : ‖((-a : ℂˣ) : ℂ)‖ = 1 := by simpa only [Units.val_neg, norm_neg] using ha
      exact complexOrdinaryEqualCoverageStep r a d ds es hds he hId hIe
        (adjacentCoverage_of_equalCoverage r (-a) ha' (ih (-a) ha')) D
  exact fun r a ha => ⟨hEq r a ha, adjacentCoverage_of_equalCoverage r a ha (hEq r a ha)⟩

/-- Ordinary normalized integrals for irreducible complex inducing lists have a finite sum
identically one in equal and adjacent ranks at each unit-modulus trace scale. -/
def ComplexOrdinaryEqualAdjacentGenerationStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ), ‖(a : ℂ)‖ = 1 →
    (∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
      IsIrreducibleGKModule (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds) →
      IsIrreducibleGKModule (complexStandardRep (r + 1) es) (complexStandardLie (r + 1) es) →
      ∀ D : ComplexQuotientMeasureData r,
        HasFiniteOrdinaryNormalizationSum (complexOrdinaryEqualTest r ds es a D) (complexPairLFactor ds es)) ∧
    (∀ (ds es : List ComplexCharacterData), ds.length = r + 2 → es.length = r + 1 →
      IsIrreducibleGKModule (complexStandardRep (r + 2) ds) (complexStandardLie (r + 2) ds) →
      IsIrreducibleGKModule (complexStandardRep (r + 1) es) (complexStandardLie (r + 1) es) →
      ∀ D : ComplexQuotientMeasureData r,
        HasFiniteOrdinaryNormalizationSum (complexOrdinaryUnequalTest (Nat.lt_succ_self r) ds es a D)
          (complexPairLFactor ds es))

theorem complexOrdinaryEqualAdjacentGeneration : ComplexOrdinaryEqualAdjacentGenerationStatement := by
  intro r a ha
  obtain ⟨hEq, hAdj⟩ := complexOrdinaryEqualAdjacentCoverage r a ha
  obtain ⟨hPE, hPA⟩ := complexOrdinaryPolynomial r a ha
  constructor
  · intro ds es hd he hId hIe D
    refine complexEqualFiniteSumFromPolynomials r ds es hd he a (2 * Real.pi) D ?_
      (hEq ds es hd he hId hIe D)
    rintro ⟨W, V, φ⟩
    obtain ⟨N, P, hP⟩ := hPE ds es hd he D W V φ.val φ.2
    exact ⟨P, N, congrFun hP⟩
  · intro ds es hd he hId hIe D
    refine complexUnequalFiniteSumFromPolynomials (r + 1) r (Nat.lt_succ_self r) ds es a D ?_
      (hAdj ds es hd he hId hIe D)
    rintro ⟨W, V⟩
    obtain ⟨N, P, hP⟩ := hPA ds es hd he D W V
    exact ⟨P, N, congrFun hP⟩

end Langlands.Global.RankinSelbergGlobal
