import Langlands.GroupScheme.Torus.WeilRestrictionSeparable
import Langlands.GroupScheme.Torus.WeilRestrictionNormSplit

/-! # Finite-separable norm and scalar maps on Galois lattices -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Algebra.SeparableTensor
open scoped TensorProduct

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K] [Algebra.IsSeparable k K]
  (hsplit : ∀ x : K, ((minpoly k x).map (algebraMap k Ω)).Splits)

local notation "W_Ω" =>
  (Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k Ω))
    (commGroupScheme (CommRingCat.of k) K))

include hsplit in
/-- The determinant norm is the product of the canonical embedding evaluations,
over every coefficient algebra. -/
theorem separableEmbedding_tensorNorm (R : Type u) [CommRing R]
    [Algebra Ω R] [Algebra k R] [IsScalarTower k Ω R] (x : K ⊗[k] R) :
    Langlands.Algebra.tensorNorm k K R x =
      ∏ τ : K →ₐ[k] Ω, tensorCoordinate (IsScalarTower.toAlgHom k Ω R) τ x := by
  classical
  rw [tensorNorm_decomposition k Ω K R (K →ₐ[k] Ω)
    (separableEmbeddingDecomposition k K Ω hsplit)]
  simp_rw [separableEmbeddingDecomposition, embeddingDecompositionTensorEquiv_apply]

/-- The actual base-changed norm multiplies the embedding coordinates on every test. -/
theorem separableEmbedding_normHom_points (T : Over (Spec (CommRingCat.of Ω)))
    (x : T ⟶ (W_Ω).X) :
    Gm.pointsEquiv (Spec (CommRingCat.of Ω)) T
        (x ≫ (CommGroupScheme.groupHom
          (decompositionNormHom (CommRingCat.of k) (CommRingCat.of Ω) K)).hom.hom) =
      ∏ τ, embeddingPointsEquiv k K Ω
        (embeddingEvaluationStatement k K Ω hsplit) T x τ := by
  classical
  exact decompositionNormHom_points (CommRingCat.of k) (CommRingCat.of Ω) K
    (K →ₐ[k] Ω) (separableEmbeddingDecomposition k K Ω hsplit) T x

/-- The actual base-changed scalar map is diagonal in the embedding coordinates. -/
theorem separableEmbedding_scalarHom_points (T : Over (Spec (CommRingCat.of Ω)))
    (x : T ⟶ (Gm (Spec (CommRingCat.of Ω))).X) :
    embeddingPointsEquiv k K Ω (embeddingEvaluationStatement k K Ω hsplit) T
        (x ≫ (CommGroupScheme.groupHom
          (decompositionScalarHom (CommRingCat.of k) (CommRingCat.of Ω) K)).hom.hom) =
      fun _ => Gm.pointsEquiv (Spec (CommRingCat.of Ω)) T x :=
  decompositionScalarHom_points (CommRingCat.of k) (CommRingCat.of Ω) K
    (K →ₐ[k] Ω) (separableEmbeddingDecomposition k K Ω hsplit) T x

/-- The actual norm character is the all-ones vector in the canonical lattice. -/
theorem separableEmbeddingCharacterEquiv_normHom :
    separableEmbeddingCharacterEquiv k K Ω hsplit
        (decompositionNormHom (CommRingCat.of k) (CommRingCat.of Ω) K) = fun _ => 1 :=
  decompositionCharacterEquiv_normHom (CommRingCat.of k) Ω K
    (K →ₐ[k] Ω) (separableEmbeddingDecomposition k K Ω hsplit)

/-- The actual scalar cocharacter is the all-ones vector in the canonical lattice. -/
theorem separableEmbeddingCocharacterEquiv_scalarHom :
    separableEmbeddingCocharacterEquiv k K Ω hsplit
        (decompositionScalarHom (CommRingCat.of k) (CommRingCat.of Ω) K) = fun _ => 1 :=
  decompositionCocharacterEquiv_scalarHom (CommRingCat.of k) Ω K
    (K →ₐ[k] Ω) (separableEmbeddingDecomposition k K Ω hsplit)

include hsplit in
/-- Every coefficient automorphism fixes the actual base-changed norm character. -/
theorem separableEmbedding_galoisRepresentation_normHom (σ : Ω ≃ₐ[k] Ω) :
    characterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ
        (decompositionNormHom (CommRingCat.of k) (CommRingCat.of Ω) K) =
      decompositionNormHom (CommRingCat.of k) (CommRingCat.of Ω) K := by
  apply (separableEmbeddingCharacterEquiv k K Ω hsplit).injective
  rw [separableEmbeddingCharacterEquiv_galoisRepresentation,
    separableEmbeddingCharacterEquiv_normHom]
  rfl

include hsplit in
/-- Every coefficient automorphism fixes the actual base-changed scalar cocharacter. -/
theorem separableEmbedding_galoisRepresentation_scalarHom (σ : Ω ≃ₐ[k] Ω) :
    cocharacterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ
        (decompositionScalarHom (CommRingCat.of k) (CommRingCat.of Ω) K) =
      decompositionScalarHom (CommRingCat.of k) (CommRingCat.of Ω) K := by
  apply (separableEmbeddingCocharacterEquiv k K Ω hsplit).injective
  rw [separableEmbeddingCocharacterEquiv_galoisRepresentation,
    separableEmbeddingCocharacterEquiv_scalarHom]
  rfl

/-- The intrinsic integer augmentation on cocharacters induced by the actual norm. -/
def separableEmbeddingNormAugmentation : cocharacterLattice W_Ω →ₗ[ℤ] ℤ :=
  latticePairing W_Ω (decompositionNormHom (CommRingCat.of k) (CommRingCat.of Ω) K)

/-- The intrinsic integer augmentation on characters induced by scalar restriction. -/
def separableEmbeddingScalarAugmentation : characterLattice W_Ω →ₗ[ℤ] ℤ :=
  (latticePairing W_Ω).flip
    (decompositionScalarHom (CommRingCat.of k) (CommRingCat.of Ω) K)

/-- Norm augmentation sums the canonical cocharacter coordinates. -/
theorem separableEmbeddingNormAugmentation_eq_sum (ν : cocharacterLattice W_Ω) :
    separableEmbeddingNormAugmentation k K Ω ν =
      ∑ τ, separableEmbeddingCocharacterEquiv k K Ω hsplit ν τ :=
  decomposition_latticePairing_normHom (CommRingCat.of k) Ω K
    (K →ₐ[k] Ω) (separableEmbeddingDecomposition k K Ω hsplit) ν

/-- Scalar restriction sums the canonical character coordinates. -/
theorem separableEmbeddingScalarAugmentation_eq_sum (χ : characterLattice W_Ω) :
    separableEmbeddingScalarAugmentation k K Ω χ =
      ∑ τ, separableEmbeddingCharacterEquiv k K Ω hsplit χ τ :=
  decomposition_latticePairing_scalarHom (CommRingCat.of k) Ω K
    (K →ₐ[k] Ω) (separableEmbeddingDecomposition k K Ω hsplit) χ

include hsplit in
/-- Norm augmentation is equivariant for the trivial action on the integers. -/
theorem separableEmbeddingNormAugmentation_galoisRepresentation
    (σ : Ω ≃ₐ[k] Ω) (ν : cocharacterLattice W_Ω) :
    separableEmbeddingNormAugmentation k K Ω
        (cocharacterLattice.galoisRepresentation k Ω
          (commGroupScheme (CommRingCat.of k) K) σ ν) =
      separableEmbeddingNormAugmentation k K Ω ν := by
  rw [separableEmbeddingNormAugmentation_eq_sum k K Ω hsplit,
    separableEmbeddingNormAugmentation_eq_sum k K Ω hsplit,
    separableEmbeddingCocharacterEquiv_galoisRepresentation]
  exact (embeddingPermutation k K Ω σ).symm.sum_comp
    (separableEmbeddingCocharacterEquiv k K Ω hsplit ν)

include hsplit in
/-- Scalar restriction is equivariant for the trivial action on the integers. -/
theorem separableEmbeddingScalarAugmentation_galoisRepresentation
    (σ : Ω ≃ₐ[k] Ω) (χ : characterLattice W_Ω) :
    separableEmbeddingScalarAugmentation k K Ω
        (characterLattice.galoisRepresentation k Ω
          (commGroupScheme (CommRingCat.of k) K) σ χ) =
      separableEmbeddingScalarAugmentation k K Ω χ := by
  rw [separableEmbeddingScalarAugmentation_eq_sum k K Ω hsplit,
    separableEmbeddingScalarAugmentation_eq_sum k K Ω hsplit,
    separableEmbeddingCharacterEquiv_galoisRepresentation]
  exact (embeddingPermutation k K Ω σ).symm.sum_comp
    (separableEmbeddingCharacterEquiv k K Ω hsplit χ)

include hsplit in
/-- Pairing the actual norm with scalar inclusion gives the field extension degree. -/
theorem separableEmbedding_latticePairing_norm_scalar :
    latticePairing W_Ω
        (decompositionNormHom (CommRingCat.of k) (CommRingCat.of Ω) K)
        (decompositionScalarHom (CommRingCat.of k) (CommRingCat.of Ω) K) =
      (Module.finrank k K : ℤ) := by
  change separableEmbeddingNormAugmentation k K Ω _ = _
  rw [separableEmbeddingNormAugmentation_eq_sum k K Ω hsplit,
    separableEmbeddingCocharacterEquiv_scalarHom]
  simp [separableEmbedding_card k K Ω hsplit]

end Langlands.GroupScheme.WeilGm
