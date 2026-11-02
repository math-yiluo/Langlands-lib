import Langlands.GroupScheme.Torus.WeilRestrictionEmbeddings

/-! # Embedding lattices of the Weil-restricted multiplicative group -/

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Algebra.SeparableTensor

namespace Langlands.GroupScheme.WeilGm

variable (k K Ω : Type u) [CommRing k] [CommRing K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [Module.Finite k K] [Module.Projective k K]
  [Finite (K →ₐ[k] Ω)] (h : Function.Bijective (embeddingEvaluation k K Ω))

local notation "W_Ω" =>
  (Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k Ω))
    (commGroupScheme (CommRingCat.of k) K))

/-- The actual character lattice in the canonical embedding coordinates. -/
def embeddingCharacterEquiv : characterLattice W_Ω ≃+ ((K →ₐ[k] Ω) → ℤ) :=
  decompositionCharacterEquiv (CommRingCat.of k) Ω K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h)

/-- The actual cocharacter lattice in the same embedding coordinates. -/
def embeddingCocharacterEquiv : cocharacterLattice W_Ω ≃+ ((K →ₐ[k] Ω) → ℤ) :=
  decompositionCocharacterEquiv (CommRingCat.of k) Ω K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h)

/-- Characters are monomials on every test scheme. -/
theorem embeddingCharacterEquiv_symm_points [Fintype (K →ₐ[k] Ω)]
    (m : (K →ₐ[k] Ω) → ℤ) (T : Over (Spec (CommRingCat.of Ω))) (x : T ⟶ (W_Ω).X) :
    Gm.pointsEquiv _ T
        (x ≫ (CommGroupScheme.groupHom ((embeddingCharacterEquiv k K Ω h).symm m)).hom.hom) =
      ∏ τ, embeddingPointsEquiv k K Ω h T x τ ^ m τ :=
  decompositionCharacterEquiv_symm_points (CommRingCat.of k) Ω K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h) m T x

/-- Cocharacters raise the parameter to the indicated power at each embedding. -/
theorem embeddingCocharacterEquiv_symm_points (m : (K →ₐ[k] Ω) → ℤ)
    (T : Over (Spec (CommRingCat.of Ω))) (x : T ⟶ (Gm (Spec (CommRingCat.of Ω))).X) :
    embeddingPointsEquiv k K Ω h T
        (x ≫ (CommGroupScheme.groupHom ((embeddingCocharacterEquiv k K Ω h).symm m)).hom.hom) =
      fun τ => Gm.pointsEquiv _ T x ^ m τ :=
  decompositionCocharacterEquiv_symm_points (CommRingCat.of k) Ω K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h) m T x

/-- The pairing on the actual lattices is the dot product in embedding coordinates. -/
theorem embedding_latticePairing_eq_sum [Fintype (K →ₐ[k] Ω)]
    (χ : characterLattice W_Ω) (ν : cocharacterLattice W_Ω) :
    latticePairing W_Ω χ ν =
      ∑ τ, embeddingCharacterEquiv k K Ω h χ τ * embeddingCocharacterEquiv k K Ω h ν τ :=
  decomposition_latticePairing_eq_sum (CommRingCat.of k) Ω K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h) χ ν

include h in
/-- The pairing of the actual character and cocharacter lattices is perfect. -/
theorem embedding_latticePairing_isPerfPair : (latticePairing W_Ω).IsPerfPair :=
  decomposition_latticePairing_isPerfPair (CommRingCat.of k) Ω K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h)

/-- The actual Galois action on characters agrees with inverse pullback on embeddings. -/
theorem galoisRepresentation_embeddingCharacterEquiv_symm (σ : Ω ≃ₐ[k] Ω)
    (m : (K →ₐ[k] Ω) → ℤ) :
    characterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ
        ((embeddingCharacterEquiv k K Ω h).symm m) =
      (embeddingCharacterEquiv k K Ω h).symm (embeddingPermutationRepresentation k K Ω σ m) := by
  classical
  let _ : Fintype (K →ₐ[k] Ω) := Fintype.ofFinite _
  apply characterLattice.ext_points
  intro T x
  rw [characterLattice.galoisRepresentation_points,
    embeddingCharacterEquiv_symm_points, embeddingCharacterEquiv_symm_points]
  refine Eq.trans ?_ (embeddingPermutationRepresentation_prod k K Ω σ m
    (embeddingPointsEquiv k K Ω h T x))
  apply Finset.prod_congr rfl
  intro τ _
  exact congrArg (fun a : (Γ(T.left, ⊤))ˣ => a ^ m τ)
    (embeddingPointsEquiv_descentPoint k K Ω h σ T x τ)

/-- The embedding-coordinate equivalence intertwines the actual character Galois action. -/
theorem embeddingCharacterEquiv_galoisRepresentation (σ : Ω ≃ₐ[k] Ω)
    (χ : characterLattice W_Ω) :
    embeddingCharacterEquiv k K Ω h
        (characterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ χ) =
      embeddingPermutationRepresentation k K Ω σ (embeddingCharacterEquiv k K Ω h χ) := by
  conv_lhs => rw [← (embeddingCharacterEquiv k K Ω h).symm_apply_apply χ]
  rw [galoisRepresentation_embeddingCharacterEquiv_symm, AddEquiv.apply_symm_apply]

/-- The actual Galois action on cocharacters is the same permutation action. -/
theorem galoisRepresentation_embeddingCocharacterEquiv_symm (σ : Ω ≃ₐ[k] Ω)
    (m : (K →ₐ[k] Ω) → ℤ) :
    cocharacterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ
        ((embeddingCocharacterEquiv k K Ω h).symm m) =
      (embeddingCocharacterEquiv k K Ω h).symm (embeddingPermutationRepresentation k K Ω σ m) := by
  apply cocharacterLattice.ext_points
  intro T x
  apply (embeddingPointsEquiv k K Ω h T).injective
  funext τ
  have hd := embeddingPointsEquiv_descentPoint k K Ω h σ T
    (x ≫ (CommGroupScheme.groupHom
      (cocharacterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ
        ((embeddingCocharacterEquiv k K Ω h).symm m))).hom.hom)
    ((embeddingPermutation k K Ω σ).symm τ)
  rw [cocharacterLattice.descentPoint_galoisRepresentation,
    embeddingCocharacterEquiv_symm_points, MulEquiv.apply_symm_apply] at hd
  rw [Equiv.apply_symm_apply] at hd
  rw [embeddingCocharacterEquiv_symm_points]
  exact hd.symm

/-- The embedding-coordinate equivalence intertwines the actual cocharacter Galois action. -/
theorem embeddingCocharacterEquiv_galoisRepresentation (σ : Ω ≃ₐ[k] Ω)
    (ν : cocharacterLattice W_Ω) :
    embeddingCocharacterEquiv k K Ω h
        (cocharacterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ ν) =
      embeddingPermutationRepresentation k K Ω σ (embeddingCocharacterEquiv k K Ω h ν) := by
  conv_lhs => rw [← (embeddingCocharacterEquiv k K Ω h).symm_apply_apply ν]
  rw [galoisRepresentation_embeddingCocharacterEquiv_symm, AddEquiv.apply_symm_apply]

include h in
/-- Simultaneous Galois transport preserves the actual lattice pairing. -/
theorem embedding_latticePairing_galoisRepresentation (σ : Ω ≃ₐ[k] Ω)
    (χ : characterLattice W_Ω) (ν : cocharacterLattice W_Ω) :
    latticePairing W_Ω
        (characterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ χ)
        (cocharacterLattice.galoisRepresentation k Ω (commGroupScheme (CommRingCat.of k) K) σ ν) =
      latticePairing W_Ω χ ν := by
  classical
  let _ : Fintype (K →ₐ[k] Ω) := Fintype.ofFinite _
  rw [embedding_latticePairing_eq_sum k K Ω h,
    embedding_latticePairing_eq_sum k K Ω h,
    embeddingCharacterEquiv_galoisRepresentation, embeddingCocharacterEquiv_galoisRepresentation]
  exact embeddingPermutationRepresentation_dotProduct k K Ω σ _ _

end Langlands.GroupScheme.WeilGm
