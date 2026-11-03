import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Langlands.Algebra.EmbeddingContinuity

/-! # Continuous Galois actions on actual norm-one lattices -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K]

/-- Continuous inverse pullback on the sum-zero embedding lattice. -/
def embeddingSumZeroContinuousRepresentation :
    C((Ω ≃ₐ[k] Ω) × (embeddingCoordinateSum k K Ω).ker,
      (embeddingCoordinateSum k K Ω).ker) where
  toFun p := embeddingSumZeroRepresentation k K Ω p.1 p.2
  continuous_toFun := by
    have hf : Continuous (fun p : (Ω ≃ₐ[k] Ω) × (embeddingCoordinateSum k K Ω).ker =>
        embeddingPermutationRepresentation k K Ω p.1 p.2.val) :=
      (embeddingContinuousRepresentation k K Ω).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact hf.subtype_mk _

@[simp] theorem embeddingSumZeroContinuousRepresentation_apply (σ : Ω ≃ₐ[k] Ω)
    (n : (embeddingCoordinateSum k K Ω).ker) :
    embeddingSumZeroContinuousRepresentation k K Ω (σ, n) =
      embeddingSumZeroRepresentation k K Ω σ n := rfl

section Quotient

variable [TopologicalSpace (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω)]
  [DiscreteTopology (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω)]

/-- Continuous inverse pullback on the discrete embedding lattice modulo constants. -/
def embeddingQuotientContinuousRepresentation :
    C((Ω ≃ₐ[k] Ω) × (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω),
      (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω)) where
  toFun p := embeddingQuotientRepresentation k K Ω p.1 p.2
  continuous_toFun := by
    rw [continuous_prod_of_discrete_right]
    intro q
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (embeddingDiagonal k K Ω) q
    change Continuous (fun σ : Ω ≃ₐ[k] Ω =>
      (Submodule.Quotient.mk (embeddingPermutationRepresentation k K Ω σ m) :
        ((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω))
    exact (continuous_of_discreteTopology (f :=
      (Submodule.Quotient.mk : ((K →ₐ[k] Ω) → ℤ) →
        (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω)))).comp
      ((embeddingContinuousRepresentation k K Ω).continuous.comp
        (continuous_id.prodMk continuous_const))

@[simp] theorem embeddingQuotientContinuousRepresentation_apply (σ : Ω ≃ₐ[k] Ω)
    (q : ((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω) :
    embeddingQuotientContinuousRepresentation k K Ω (σ, q) =
      embeddingQuotientRepresentation k K Ω σ q := rfl

end Quotient

private abbrev normOneEmbeddingBaseChange : CommGroupScheme (Spec (CommRingCat.of.{u} Ω)) :=
  (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
    (normOneCommGroupScheme (CommRingCat.of.{u} k) K)

variable [Algebra.IsSeparable k K]
  (hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits)

local notation "N_Ω" => normOneEmbeddingBaseChange k K Ω

section Cocharacters

variable [TopologicalSpace (cocharacterLattice (normOneEmbeddingBaseChange k K Ω))]
  [DiscreteTopology (cocharacterLattice (normOneEmbeddingBaseChange k K Ω))]

/-- The continuous actual ordinary Galois action on discrete norm-one cocharacters. -/
def normOneSeparableEmbeddingCocharacterContinuousAction :
    C((Ω ≃ₐ[k] Ω) × cocharacterLattice N_Ω, cocharacterLattice N_Ω) where
  toFun p := cocharacterLattice.galoisRepresentation k Ω
    (normOneCommGroupScheme (CommRingCat.of k) K) p.1 p.2
  continuous_toFun := by
    let e := normOneSeparableEmbeddingCocharacterEquiv k K Ω hsplit
    have he : Continuous e := continuous_of_discreteTopology
    have hei : Continuous e.symm := continuous_of_discreteTopology
    have hf := hei.comp ((embeddingSumZeroContinuousRepresentation k K Ω).continuous.comp
      (continuous_fst.prodMk (he.comp continuous_snd)))
    refine hf.congr fun p => ?_
    apply e.injective
    exact (e.apply_symm_apply _).trans
      (normOneSeparableEmbeddingCocharacterEquiv_equivariant k K Ω hsplit p.1 p.2).symm

@[simp] theorem normOneSeparableEmbeddingCocharacterContinuousAction_apply
    (σ : Ω ≃ₐ[k] Ω) (ν : cocharacterLattice N_Ω) :
    normOneSeparableEmbeddingCocharacterContinuousAction k K Ω hsplit (σ, ν) =
      cocharacterLattice.galoisRepresentation k Ω
        (normOneCommGroupScheme (CommRingCat.of k) K) σ ν := rfl

end Cocharacters

section Characters

variable [TopologicalSpace (characterLattice (normOneEmbeddingBaseChange k K Ω))]
  [DiscreteTopology (characterLattice (normOneEmbeddingBaseChange k K Ω))]

/-- The continuous actual ordinary Galois action on discrete norm-one characters. -/
def normOneSeparableEmbeddingCharacterContinuousAction :
    C((Ω ≃ₐ[k] Ω) × characterLattice N_Ω, characterLattice N_Ω) where
  toFun p := characterLattice.galoisRepresentation k Ω
    (normOneCommGroupScheme (CommRingCat.of k) K) p.1 p.2
  continuous_toFun := by
    let : TopologicalSpace (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω) := ⊥
    let : DiscreteTopology (((K →ₐ[k] Ω) → ℤ) ⧸ embeddingDiagonal k K Ω) := ⟨rfl⟩
    let e := normOneSeparableEmbeddingCharacterEquiv k K Ω hsplit
    have he : Continuous e := continuous_of_discreteTopology
    have hei : Continuous e.symm := continuous_of_discreteTopology
    have hf := hei.comp ((embeddingQuotientContinuousRepresentation k K Ω).continuous.comp
      (continuous_fst.prodMk (he.comp continuous_snd)))
    refine hf.congr fun p => ?_
    apply e.injective
    exact (e.apply_symm_apply _).trans
      (normOneSeparableEmbeddingCharacterEquiv_equivariant k K Ω hsplit p.1 p.2).symm

@[simp] theorem normOneSeparableEmbeddingCharacterContinuousAction_apply
    (σ : Ω ≃ₐ[k] Ω) (χ : characterLattice N_Ω) :
    normOneSeparableEmbeddingCharacterContinuousAction k K Ω hsplit (σ, χ) =
      characterLattice.galoisRepresentation k Ω
        (normOneCommGroupScheme (CommRingCat.of k) K) σ χ := rfl

end Characters

end Langlands.GroupScheme.WeilGm
