import Langlands.Algebra.SeparableTensorProof
import Langlands.GroupScheme.Torus.WeilRestrictionEmbeddingContinuity
import Mathlib.FieldTheory.IsSepClosed

/-! # Finite-separable Weil restriction in canonical embedding coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor
open scoped TensorProduct

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K] [Algebra.IsSeparable k K]
  (hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits)

/-- Finite separability and splitting of the minimal polynomials give the canonical
embedding decomposition of the scalar-extended algebra. -/
def separableEmbeddingDecomposition : Ω ⊗[k] K ≃ₐ[Ω] ((K →ₐ[k] Ω) → Ω) :=
  embeddingDecomposition k K Ω (embeddingEvaluationStatement k K Ω hsplit)

/-- The actual finite-separable Weil restriction splits by its embeddings. -/
def separableEmbeddingIso :
    (GroupScheme.baseChange (algebraBaseMap k Ω)).obj (groupScheme (CommRingCat.of k) K) ≅
      splitTorus (Spec (CommRingCat.of Ω)) (K →ₐ[k] Ω) :=
  embeddingIso k K Ω (embeddingEvaluationStatement k K Ω hsplit)

/-- The same canonical splitting in the commutative category. -/
def separableEmbeddingCommIso :
    (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj (commGroupScheme (CommRingCat.of k) K) ≅
      splitTorus.commGroupScheme (Spec (CommRingCat.of Ω)) (K →ₐ[k] Ω) :=
  embeddingCommIso k K Ω (embeddingEvaluationStatement k K Ω hsplit)

include hsplit in
/-- The number of canonical splitting coordinates is the degree of the source extension. -/
theorem separableEmbedding_card : Fintype.card (K →ₐ[k] Ω) = Module.finrank k K :=
  AlgHom.card_of_splits k K Ω hsplit

/-- The actual character lattice has the canonical embedding coordinates. -/
def separableEmbeddingCharacterEquiv :
    characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
      (commGroupScheme (CommRingCat.of k) K)) ≃+ ((K →ₐ[k] Ω) → ℤ) :=
  embeddingCharacterEquiv k K Ω (embeddingEvaluationStatement k K Ω hsplit)

/-- The actual cocharacter lattice has the same canonical embedding coordinates. -/
def separableEmbeddingCocharacterEquiv :
    cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
      (commGroupScheme (CommRingCat.of k) K)) ≃+ ((K →ₐ[k] Ω) → ℤ) :=
  embeddingCocharacterEquiv k K Ω (embeddingEvaluationStatement k K Ω hsplit)

/-- The actual character action is inverse pullback on the embeddings. -/
theorem separableEmbeddingCharacterEquiv_galoisRepresentation (σ : Ω ≃ₐ[k] Ω)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
      (commGroupScheme (CommRingCat.of k) K))) :
    separableEmbeddingCharacterEquiv k K Ω hsplit
        (characterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ χ) =
      embeddingPermutationRepresentation k K Ω σ
        (separableEmbeddingCharacterEquiv k K Ω hsplit χ) :=
  embeddingCharacterEquiv_galoisRepresentation k K Ω
    (embeddingEvaluationStatement k K Ω hsplit) σ χ

/-- The actual cocharacter action is the same inverse pullback. -/
theorem separableEmbeddingCocharacterEquiv_galoisRepresentation (σ : Ω ≃ₐ[k] Ω)
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
      (commGroupScheme (CommRingCat.of k) K))) :
    separableEmbeddingCocharacterEquiv k K Ω hsplit
        (cocharacterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ ν) =
      embeddingPermutationRepresentation k K Ω σ
        (separableEmbeddingCocharacterEquiv k K Ω hsplit ν) :=
  embeddingCocharacterEquiv_galoisRepresentation k K Ω
    (embeddingEvaluationStatement k K Ω hsplit) σ ν

private abbrev separableEmbeddingBaseChange : CommGroupScheme (Spec (CommRingCat.of Ω)) :=
  (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj
    (commGroupScheme (CommRingCat.of k) K)

local notation "W_Ω" => separableEmbeddingBaseChange k K Ω

section Characters

variable [TopologicalSpace (characterLattice (separableEmbeddingBaseChange k K Ω))]
  [DiscreteTopology (characterLattice (separableEmbeddingBaseChange k K Ω))]

/-- The finite-separable actual character action is jointly continuous for the Krull
topology and a discrete lattice topology. -/
def separableEmbeddingCharacterContinuousAction :
    C((Ω ≃ₐ[k] Ω) × characterLattice W_Ω, characterLattice W_Ω) :=
  embeddingCharacterContinuousAction k K Ω (embeddingEvaluationStatement k K Ω hsplit)

@[simp] theorem separableEmbeddingCharacterContinuousAction_apply
    (σ : Ω ≃ₐ[k] Ω) (χ : characterLattice W_Ω) :
    separableEmbeddingCharacterContinuousAction k K Ω hsplit (σ, χ) =
      characterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ χ :=
  rfl

end Characters

section Cocharacters

variable [TopologicalSpace (cocharacterLattice (separableEmbeddingBaseChange k K Ω))]
  [DiscreteTopology (cocharacterLattice (separableEmbeddingBaseChange k K Ω))]

/-- The finite-separable actual cocharacter action is jointly continuous for the Krull
topology and a discrete lattice topology. -/
def separableEmbeddingCocharacterContinuousAction :
    C((Ω ≃ₐ[k] Ω) × cocharacterLattice W_Ω, cocharacterLattice W_Ω) :=
  embeddingCocharacterContinuousAction k K Ω (embeddingEvaluationStatement k K Ω hsplit)

@[simp] theorem separableEmbeddingCocharacterContinuousAction_apply
    (σ : Ω ≃ₐ[k] Ω) (ν : cocharacterLattice W_Ω) :
    separableEmbeddingCocharacterContinuousAction k K Ω hsplit (σ, ν) =
      cocharacterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ ν :=
  rfl

end Cocharacters

omit [FiniteDimensional k K] in
/-- Over a separably closed coefficient field, the splitting-polynomial input is automatic. -/
theorem separable_minpoly_splits [IsSepClosed Ω] (x : K) :
    ((minpoly k x).map (algebraMap k Ω)).Splits :=
  IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable k x)

/-- The Weil restriction of the multiplicative group through a finite separable field
extension is a torus, split by the separable closure of the base field. -/
theorem isTorus_of_finite_separable : IsTorus (groupScheme (CommRingCat.of k) K) := by
  refine ⟨SeparableClosure k, inferInstance, inferInstance, ?_⟩
  exact ⟨K →ₐ[k] SeparableClosure k, inferInstance,
    ⟨separableEmbeddingIso k K (SeparableClosure k)
      (separable_minpoly_splits k K (SeparableClosure k))⟩⟩

end Langlands.GroupScheme.WeilGm
