import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule

/-! # Normalization and generation for ordinary archimedean integrals -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean Langlands.Automorphic

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

attribute [local instance 100] LieRing.ofAssociativeRing

section NormalizedFamilies

variable {Test : Type*} (integral : Test → ℂ → ℂ) (factor : ReciprocalEntire)

/-- Every test has an entire normalization by the prescribed L-factor. -/
def HasEntireOrdinaryNormalizations : Prop :=
  ∀ i, Nonempty (OrdinaryIntegralNormalization (integral i) (fun s => (factor.denominator s)⁻¹))

/-- At every spectral point some entire normalized value is nonzero. -/
def HasCoveringOrdinaryNormalizations : Prop :=
  ∀ s : ℂ, ∃ (i : Test) (N : OrdinaryIntegralNormalization (integral i)
    (fun w => (factor.denominator w)⁻¹)), N.value s ≠ 0

/-- Finitely many ordinary normalized values sum to one on the whole plane. -/
def HasFiniteOrdinaryNormalizationSum : Prop :=
  ∃ (n : ℕ) (i : Fin n → Test)
    (N : ∀ j, OrdinaryIntegralNormalization (integral (i j)) (fun s => (factor.denominator s)⁻¹)),
    ∀ s, ∑ j, (N j).value s = 1

theorem HasFiniteOrdinaryNormalizationSum.covering
    (h : HasFiniteOrdinaryNormalizationSum integral factor) :
    HasCoveringOrdinaryNormalizations integral factor := by
  obtain ⟨n, i, N, hN⟩ := h
  intro s
  by_contra! hz
  have hsum : ∑ j : Fin n, (N j).value s = 0 := Finset.sum_eq_zero fun j _ => hz (i j) (N j)
  exact zero_ne_one (hsum.symm.trans (hN s))

end NormalizedFamilies

section TestIntegrals

/-- Ordinary unequal-rank real integral as a function of two model vectors. -/
def realOrdinaryUnequalTest {r t : ℕ} (h : t < r) (d e : List RealBlock) (a : ℝˣ)
    (D : RealQuotientMeasureData t)
    (i : Prod (realWhittakerModel r d a) (realWhittakerModel t e (-a))) : ℂ → ℂ :=
  realUnequalIntegral h D i.1 i.2

/-- Ordinary unequal-rank complex integral as a function of two model vectors. -/
def complexOrdinaryUnequalTest {r t : ℕ} (h : t < r) (d e : List ComplexCharacterData) (a : ℂˣ)
    (D : ComplexQuotientMeasureData t)
    (i : Prod (complexWhittakerModel r d a) (complexWhittakerModel t e (-a))) : ℂ → ℂ :=
  complexUnequalIntegral h D i.1 i.2

/-- Ordinary equal-rank real integral as a function of two model vectors and a Schwartz test. -/
def realOrdinaryEqualTest (r : ℕ) (d e : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData r)
    (i : Prod (realWhittakerModel r d a)
      (Prod (realWhittakerModel r e (-a)) (SchwartzMap (Fin (r + 1) → ℝ) ℂ))) : ℂ → ℂ :=
  realEqualIntegral D i.1 i.2.1 i.2.2

/-- Ordinary equal-rank complex integral as a function of two model vectors and a Schwartz test. -/
def complexOrdinaryEqualTest (r : ℕ) (d e : List ComplexCharacterData) (a : ℂˣ)
    (D : ComplexQuotientMeasureData r)
    (i : Prod (complexWhittakerModel r d a)
      (Prod (complexWhittakerModel r e (-a)) (SchwartzMap (Fin (r + 1) → ℂ) ℂ))) : ℂ → ℂ :=
  complexEqualIntegral D i.1 i.2.1 i.2.2

end TestIntegrals

/-- The ordinary continuation conclusions of Jacquet's theorem for the real coefficient models. -/
def RealOrdinaryNormalizedContinuationStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (d e : List RealBlock), realRank d = r + 1 → realRank e = t + 1 →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData t),
      HasEntireOrdinaryNormalizations (realOrdinaryUnequalTest h d e a D) (realPairLFactor d e)) ∧
  ∀ (r : ℕ) (d e : List RealBlock), realRank d = r + 1 → realRank e = r + 1 →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData r),
      HasEntireOrdinaryNormalizations (realOrdinaryEqualTest r d e a D) (realPairLFactor d e)

/-- The ordinary continuation conclusions of Jacquet's theorem for the complex coefficient models. -/
def ComplexOrdinaryNormalizedContinuationStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = t + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t),
      HasEntireOrdinaryNormalizations (complexOrdinaryUnequalTest h d e a D)
        (complexPairLFactor d e)) ∧
  ∀ (r : ℕ) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = r + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r),
      HasEntireOrdinaryNormalizations (complexOrdinaryEqualTest r d e a D) (complexPairLFactor d e)

/-- Pointwise real normalized generation, with a finite sum in equal and adjacent ranks. -/
def RealOrdinaryNormalizedGenerationStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (d e : List RealBlock), realRank d = r + 1 → realRank e = t + 1 →
    IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d) →
    IsIrreducibleGKModule (realStandardRep (t + 1) e) (realStandardLie (t + 1) e) →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData t),
      realWhittakerModel r d a ≠ ⊥ → realWhittakerModel t e (-a) ≠ ⊥ →
      HasCoveringOrdinaryNormalizations (realOrdinaryUnequalTest h d e a D) (realPairLFactor d e) ∧
      (t + 1 = r → (a = 1 ∨ a = -1) →
        HasFiniteOrdinaryNormalizationSum (realOrdinaryUnequalTest h d e a D) (realPairLFactor d e))) ∧
  ∀ (r : ℕ) (d e : List RealBlock), realRank d = r + 1 → realRank e = r + 1 →
    IsIrreducibleGKModule (realStandardRep (r + 1) d) (realStandardLie (r + 1) d) →
    IsIrreducibleGKModule (realStandardRep (r + 1) e) (realStandardLie (r + 1) e) →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData r),
      realWhittakerModel r d a ≠ ⊥ → realWhittakerModel r e (-a) ≠ ⊥ →
      HasCoveringOrdinaryNormalizations (realOrdinaryEqualTest r d e a D) (realPairLFactor d e) ∧
      ((a = 1 ∨ a = -1) →
        HasFiniteOrdinaryNormalizationSum (realOrdinaryEqualTest r d e a D) (realPairLFactor d e))

/-- Pointwise complex normalized generation, with a finite sum in equal and adjacent ranks. -/
def ComplexOrdinaryNormalizedGenerationStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = t + 1 →
    IsIrreducibleGKModule (complexStandardRep (r + 1) d) (complexStandardLie (r + 1) d) →
    IsIrreducibleGKModule (complexStandardRep (t + 1) e) (complexStandardLie (t + 1) e) →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t),
      complexWhittakerModel r d a ≠ ⊥ → complexWhittakerModel t e (-a) ≠ ⊥ →
      HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest h d e a D)
        (complexPairLFactor d e) ∧
      (t + 1 = r → (a = 1 ∨ a = -1) →
        HasFiniteOrdinaryNormalizationSum (complexOrdinaryUnequalTest h d e a D)
        (complexPairLFactor d e))) ∧
  ∀ (r : ℕ) (d e : List ComplexCharacterData), d.length = r + 1 → e.length = r + 1 →
    IsIrreducibleGKModule (complexStandardRep (r + 1) d) (complexStandardLie (r + 1) d) →
    IsIrreducibleGKModule (complexStandardRep (r + 1) e) (complexStandardLie (r + 1) e) →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r),
      complexWhittakerModel r d a ≠ ⊥ → complexWhittakerModel r e (-a) ≠ ⊥ →
      HasCoveringOrdinaryNormalizations (complexOrdinaryEqualTest r d e a D)
        (complexPairLFactor d e) ∧
      ((a = 1 ∨ a = -1) →
        HasFiniteOrdinaryNormalizationSum (complexOrdinaryEqualTest r d e a D)
          (complexPairLFactor d e))

/-- Ordinary archimedean local continuation and normalized generation in both fields. -/
def ArchimedeanOrdinaryNormalizedTestsStatement : Prop :=
  RealOrdinaryNormalizedContinuationStatement ∧ ComplexOrdinaryNormalizedContinuationStatement ∧
    RealOrdinaryNormalizedGenerationStatement ∧ ComplexOrdinaryNormalizedGenerationStatement

end Langlands.Global.RankinSelbergGlobal
