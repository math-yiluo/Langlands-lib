import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Category.Subquotients

/-!
# Finite length of normalized products of smooth GL factors

Henniart (2002), §2.5, and the block-factor specialization of Casselman
(1 May 1995), Corollary 6.3.8. These are proposition definitions, not proofs.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Normalized upper parabolic induction of a finite family of arbitrary
irreducible smooth complex GL factors has finite group-module length.
The block shape includes positivity of each rank and their sum. -/
def IrreducibleProductFiniteLength : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (B : BlockShape n)
      (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, (A i).IsIrreducible) →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        ((T.normalizedProductInductionFunctor B).obj A).representation.asModule

/-- Normalized upper parabolic product induction preserves finite length
when every smooth complex block factor is admissible and of finite length.
Admissibility alone is not the premise. -/
def AdmissibleFiniteLengthProductPreservation : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (B : BlockShape n)
      (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, (A i).IsAdmissible ∧
        IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear (B.size i) F.Carrier))
          (A i).representation.asModule) →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        ((T.normalizedProductInductionFunctor B).obj A).representation.asModule

/-- Both finite-length assertions over every finite p-adic extension and
every compatible topological realization, with independent field and factor
carrier universes. Neither assertion includes a numerical length bound. -/
def PadicNormalizedProductFiniteLengthTheorems : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    IrreducibleProductFiniteLength.{uF, uV} F T ∧
    AdmissibleFiniteLengthProductPreservation.{uF, uV} F T

end Langlands.Classification
