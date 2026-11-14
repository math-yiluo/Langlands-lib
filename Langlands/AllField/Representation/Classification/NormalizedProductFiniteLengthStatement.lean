import Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement
import Langlands.AllField.Representation.Induction.BlockFactors
/-!
# Finite length of normalized products of smooth GL factors

Henniart (2002), §2.5, and the block-factor specialization of Casselman
(1 May 1995), Corollary 6.3.8. These are proposition definitions, not proofs.
-/

namespace Langlands.AllField.Classification
open Langlands.Classification hiding AdmissibleFiniteLengthProductPreservation IrreducibleProductFiniteLength
open Langlands.AllField.Classification

open Langlands.GeneralLinear

universe uF uV

variable (F : Type uF) [Field F]
  (T : LocalFieldData F)

/-- Normalized upper parabolic induction of a finite family of arbitrary
irreducible smooth complex GL factors has finite group-module length.
The block shape includes positivity of each rank and their sum. -/
def IrreducibleProductFiniteLength : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (B : BlockShape n)
      (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F)),
      (∀ i, (A i).IsIrreducible) →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F))
        ((T.normalizedProductInductionFunctor B).obj A).representation.asModule

/-- Normalized upper parabolic product induction preserves finite length
when every smooth complex block factor is admissible and of finite length.
Admissibility alone is not the premise. -/
def AdmissibleFiniteLengthProductPreservation : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (B : BlockShape n)
      (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F)),
      (∀ i, (A i).IsAdmissible ∧
        IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear (B.size i) F))
          (A i).representation.asModule) →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F))
        ((T.normalizedProductInductionFunctor B).obj A).representation.asModule

end Langlands.AllField.Classification
