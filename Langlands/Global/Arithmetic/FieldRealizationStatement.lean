import Langlands.LocalField.Definitions
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

namespace Langlands.Global

universe u v

/-- Totally real globalization of a finite Galois extension of p-adic fields,
with the entire global Galois group realized at the selected finite place. -/
def TotallyRealGaloisRealizationStatement : Prop :=
  ∀ (p : ℕ) (_ : Fact p.Prime)
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    (_ : Algebra F.Carrier E.Carrier)
    (_ : IsScalarTower (Padic p) F.Carrier E.Carrier)
    (_ : IsGalois F.Carrier E.Carrier),
    letI := F.canonicalTopology
    letI := E.canonicalTopology
    ∃ (K L : Type) (_ : Field K) (_ : Field L)
      (_ : NumberField K) (_ : NumberField L)
      (_ : Algebra K L) (_ : IsGalois K L),
      NumberField.IsTotallyReal K ∧ NumberField.IsTotallyReal L ∧
      Module.finrank K L = Module.finrank F.Carrier E.Carrier ∧
      ∃ (vK : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        (wL : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
        (φ : vK.adicCompletion K ≃+* F.Carrier)
        (ψ : wL.adicCompletion L ≃+* E.Carrier)
        (θ : (L ≃ₐ[K] L) ≃* (E.Carrier ≃ₐ[F.Carrier] E.Carrier)),
        wL.asIdeal.LiesOver vK.asIdeal ∧
        (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          w.asIdeal.LiesOver vK.asIdeal → w = wL) ∧
        Continuous φ ∧ Continuous φ.symm ∧ Continuous ψ ∧ Continuous ψ.symm ∧
        (∀ x : K,
          ψ (algebraMap L (wL.adicCompletion L) (algebraMap K L x)) =
            algebraMap F.Carrier E.Carrier (φ (algebraMap K (vK.adicCompletion K) x))) ∧
        (∀ (σ : L ≃ₐ[K] L) (x : L),
          θ σ (ψ (algebraMap L (wL.adicCompletion L) x)) =
            ψ (algebraMap L (wL.adicCompletion L) (σ x)))

/-- A specified rational prime has exactly two places, each with completion
topologically isomorphic to the corresponding p-adic rational field. -/
def HasSplitQuadraticPrime (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] : Prop :=
  ∃ (v₁ v₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (φ₁ : v₁.adicCompletion K ≃+* Padic p)
    (φ₂ : v₂.adicCompletion K ≃+* Padic p),
    v₁ ≠ v₂ ∧
    (p : NumberField.RingOfIntegers K) ∈ v₁.asIdeal ∧
    (p : NumberField.RingOfIntegers K) ∈ v₂.asIdeal ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ v.asIdeal → v = v₁ ∨ v = v₂) ∧
    Continuous φ₁ ∧ Continuous φ₁.symm ∧ Continuous φ₂ ∧ Continuous φ₂.symm

/-- Split imaginary and real quadratic fields can be chosen with their
compositum linearly disjoint from a supplied totally real number field. -/
def SplitAuxiliaryQuadraticsStatement : Prop :=
  ∀ (p : ℕ) (_ : Fact p.Prime) (K : Type u) (_ : Field K)
    (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
    ∃ (I R : IntermediateField ℚ (AlgebraicClosure K))
      (_ : NumberField I) (_ : NumberField R),
      Module.finrank ℚ I = 2 ∧ Module.finrank ℚ R = 2 ∧
      NumberField.IsTotallyComplex I ∧ NumberField.IsTotallyReal R ∧
      I.LinearDisjoint R ∧ (I ⊔ R).LinearDisjoint K ∧
      HasSplitQuadraticPrime p I ∧ HasSplitQuadraticPrime p R

/-- The field-realization and auxiliary splitting inputs for the global
construction in Henniart (2000), Section 3.3. -/
def FieldRealizationStatement : Prop :=
  TotallyRealGaloisRealizationStatement.{u, v} ∧
    SplitAuxiliaryQuadraticsStatement.{u}

end Langlands.Global
