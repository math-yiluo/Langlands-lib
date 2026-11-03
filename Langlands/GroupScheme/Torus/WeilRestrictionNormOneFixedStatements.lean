import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Mathlib.FieldTheory.Normal.Basic

/-! # Fixed-lattice targets for the actual norm-one torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω]

/-- Every pair of embeddings is related by postcomposition with a coefficient automorphism. -/
def embeddingActionTransitiveStatement : Prop :=
  ∀ τ υ : K →ₐ[k] Ω, ∃ σ : Ω ≃ₐ[k] Ω,
    embeddingPermutation k K Ω σ τ = υ

variable [FiniteDimensional k K]

/-- The only fixed vector in the sum-zero embedding lattice is zero. -/
def embeddingSumZeroFixedStatement : Prop :=
  ∀ m : (embeddingCoordinateSum k K Ω).ker,
    (∀ σ : Ω ≃ₐ[k] Ω, embeddingSumZeroRepresentation k K Ω σ m = m) ↔ m = 0

/-- The only fixed class in the embedding lattice modulo constants is zero. -/
def embeddingQuotientFixedStatement : Prop :=
  ∀ m : (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω),
    (∀ σ : Ω ≃ₐ[k] Ω, embeddingQuotientRepresentation k K Ω σ m = m) ↔ m = 0

/-- The ordinary Galois action on actual norm-one cocharacters has no nonzero fixed vector. -/
def normOneCocharacterFixedStatement : Prop :=
  ∀ ν : cocharacterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
        (normOneCommGroupScheme (CommRingCat.of k) K)),
    (∀ σ : Ω ≃ₐ[k] Ω,
      cocharacterLattice.galoisRepresentation k Ω
        (normOneCommGroupScheme (CommRingCat.of k) K) σ ν = ν) ↔ ν = 0

/-- The ordinary Galois action on actual norm-one characters has no nonzero fixed vector. -/
def normOneCharacterFixedStatement : Prop :=
  ∀ χ : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
        (normOneCommGroupScheme (CommRingCat.of k) K)),
    (∀ σ : Ω ≃ₐ[k] Ω,
      characterLattice.galoisRepresentation k Ω
        (normOneCommGroupScheme (CommRingCat.of k) K) σ χ = χ) ↔ χ = 0

/-- Finite separability, normal coefficients and explicit splitting imply embedding
transitivity and fixed-vector vanishing in both coordinate and actual norm-one lattices. -/
def normOneGaloisFixedLatticesStatement : Prop :=
  Algebra.IsSeparable k K →
  Normal k Ω →
  (∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits) →
  embeddingActionTransitiveStatement k K Ω ∧
    embeddingSumZeroFixedStatement k K Ω ∧
    embeddingQuotientFixedStatement k K Ω ∧
    normOneCocharacterFixedStatement k K Ω ∧
    normOneCharacterFixedStatement k K Ω

end Langlands.GroupScheme.WeilGm
