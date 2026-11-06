import Langlands.GroupScheme.Torus.WeilRestrictionProductDecomposition

/-! # Characters of Weil restrictions from products of intermediate fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.Algebra.SeparableTensor

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {I : Type u} [Fintype I] [DecidableEq I] (E : I → IntermediateField k L)

@[simp] theorem productEmbeddingDecomposition_tmul (c : L) (a : ∀ i, E i)
    (j : Σ i, E i →ₐ[k] L) :
    productEmbeddingDecomposition k L E (c ⊗ₜ a) j = c * j.2 (a j.1) := rfl

/-- An indexed coordinate evaluates the selected factor of the product algebra. -/
def productEmbedding (j : Σ i, E i →ₐ[k] L) : (∀ i, E i) →ₐ[k] L :=
  j.2.comp (Pi.evalAlgHom k (fun i => E i) j.1)

/-- The tensor decomposition evaluates at the corresponding indexed algebra map. -/
theorem productEmbeddingDecompositionTensorEquiv_apply
    (R : Type u) [CommRing R] [Algebra L R] [Algebra k R] [IsScalarTower k L R]
    (x : (∀ i, E i) ⊗[k] R) (j : Σ i, E i →ₐ[k] L) :
    decompositionTensorEquiv k L (∀ i, E i) R (Σ i, E i →ₐ[k] L)
        (productEmbeddingDecomposition k L E) x j =
      tensorCoordinate (IsScalarTower.toAlgHom k L R) (productEmbedding k L E j) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a r => simp [productEmbedding, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

private abbrev productEmbeddingBaseChange :=
  (CommGroupScheme.baseChange (algebraBaseMap k L)).obj
    (commGroupScheme (CommRingCat.of k) (∀ i, E i))

local notation "W_L" => productEmbeddingBaseChange k L E

/-- The actual base-changed Weil restriction splits in indexed embedding coordinates. -/
def productEmbeddingCommIso :
    W_L ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of L)) (Σ i, E i →ₐ[k] L) :=
  commDecompositionIso (CommRingCat.of k) (CommRingCat.of L) (∀ i, E i)
    (Σ i, E i →ₐ[k] L) (productEmbeddingDecomposition k L E)

/-- Indexed embedding coordinates on every test scheme. -/
def productEmbeddingPointsEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (W_L).X) ≃* ((Σ i, E i →ₐ[k] L) → (Γ(T.left, ⊤))ˣ) :=
  decompositionPointsEquiv (CommRingCat.of k) (CommRingCat.of L) (∀ i, E i)
    (Σ i, E i →ₐ[k] L) (productEmbeddingDecomposition k L E) T

theorem productEmbeddingPointsEquiv_apply (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (W_L).X) (j : Σ i, E i →ₐ[k] L) :
    productEmbeddingPointsEquiv k L E T x j =
      Units.map (tensorCoordinate (embeddingCoefficientMap k L T)
        (productEmbedding k L E j)).toMonoidHom
        (pointsEquiv (CommRingCat.of k) (∀ i, E i)
          ((Over.map (algebraBaseMap k L)).obj T)
          (GroupScheme.baseChangePointsEquiv (algebraBaseMap k L)
            (groupScheme (CommRingCat.of k) (∀ i, E i)) T x)) := by
  let := restrictedSectionsAlgebra (CommRingCat.of k) (CommRingCat.of L) T
  let := restrictedSectionsScalarTower (CommRingCat.of k) (CommRingCat.of L) T
  apply Units.ext
  exact productEmbeddingDecompositionTensorEquiv_apply
    (CommRingCat.of k) (CommRingCat.of L) E
    (restrictedSections (CommRingCat.of k) (CommRingCat.of L) T) _ j

/-- Postcomposition acts separately on the embeddings of each intermediate field. -/
def productEmbeddingPermutation (σ : L ≃ₐ[k] L) :
    Equiv.Perm (Σ i, E i →ₐ[k] L) :=
  Equiv.sigmaCongrRight (fun i => embeddingPermutation k (E i) L σ)

omit [FiniteDimensional k L] [IsGalois k L] [Fintype I] [DecidableEq I] in
@[simp] theorem productEmbeddingPermutation_apply (σ : L ≃ₐ[k] L)
    (j : Σ i, E i →ₐ[k] L) :
    productEmbeddingPermutation k L E σ j = ⟨j.1, σ.toAlgHom.comp j.2⟩ := rfl

/-- The postcomposition permutations respect multiplication of automorphisms. -/
def productEmbeddingPermutationHom : (L ≃ₐ[k] L) →* Equiv.Perm (Σ i, E i →ₐ[k] L) where
  toFun := productEmbeddingPermutation k L E
  map_one' := by
    apply Equiv.ext
    rintro ⟨i, τ⟩
    apply Sigma.ext rfl
    exact heq_of_eq (AlgHom.ext fun _ => rfl)
  map_mul' _ _ := by
    apply Equiv.ext
    rintro ⟨i, τ⟩
    apply Sigma.ext rfl
    exact heq_of_eq (AlgHom.ext fun _ => rfl)

/-- Twisting coefficients postcomposes the indexed embedding coordinate. -/
theorem productEmbeddingPointsEquiv_descentPoint (σ : L ≃ₐ[k] L)
    (T : Over (Spec (CommRingCat.of L))) (x : T ⟶ (W_L).X)
    (j : Σ i, E i →ₐ[k] L) :
    productEmbeddingPointsEquiv k L E ((Over.map (galoisBaseMap k L σ)).obj T)
        (descentPoint (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ)
          (commGroupScheme (CommRingCat.of k) (∀ i, E i)).toGrp T x) j =
      productEmbeddingPointsEquiv k L E T x (productEmbeddingPermutation k L E σ j) := by
  rw [productEmbeddingPointsEquiv_apply, productEmbeddingPointsEquiv_apply,
    baseChangePointsEquiv_descentPoint, pointsEquiv_naturality]
  apply Units.ext
  change tensorCoordinate _ (productEmbedding k L E j)
    (Algebra.TensorProduct.lTensor (S := (∀ i, E i)) (∀ i, E i)
      ((algΓ (CommRingCat.of k)).map
        (descentTestIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) T).inv).unop.hom _) = _
  rw [embeddingCoefficientMap_descent_eq, tensorCoordinate_natural, tensorCoordinate_comp]
  change (𝟙 T.left : T.left ⟶ T.left).appTop.hom _ = _
  rw [Scheme.Hom.id_appTop]
  rfl

/-- The actual character lattice in indexed embedding coordinates. -/
def productEmbeddingCharacterEquiv : characterLattice W_L ≃+ ((Σ i, E i →ₐ[k] L) → ℤ) :=
  decompositionCharacterEquiv (CommRingCat.of k) L (∀ i, E i)
    (Σ i, E i →ₐ[k] L) (productEmbeddingDecomposition k L E)

/-- Characters evaluate as monomials in the indexed coordinates. -/
theorem productEmbeddingCharacterEquiv_symm_points
    (m : (Σ i, E i →ₐ[k] L) → ℤ) (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (W_L).X) :
    Gm.pointsEquiv _ T
        (x ≫ (CommGroupScheme.groupHom
          ((productEmbeddingCharacterEquiv k L E).symm m)).hom.hom) =
      ∏ j, productEmbeddingPointsEquiv k L E T x j ^ m j := by
  unfold productEmbeddingCharacterEquiv productEmbeddingPointsEquiv
  rw [decompositionCharacterEquiv_symm_eq, comp_groupHom_comp,
    splitTorus.pointsEquiv_characterLatticeEquiv_symm, commDecompositionIso_hom_points]

/-- Actual character transport is inverse postcomposition on the embedding indices. -/
theorem galoisRepresentation_productEmbeddingCharacterEquiv_symm
    (σ : L ≃ₐ[k] L) (m : (Σ i, E i →ₐ[k] L) → ℤ) :
    characterLattice.galoisRepresentation k L
        (commGroupScheme (CommRingCat.of k) (∀ i, E i)) σ
        ((productEmbeddingCharacterEquiv k L E).symm m) =
      (productEmbeddingCharacterEquiv k L E).symm
        (fun j => m ⟨j.1, σ.symm.toAlgHom.comp j.2⟩) := by
  classical
  apply characterLattice.ext_points
  intro T x
  rw [characterLattice.galoisRepresentation_points,
    productEmbeddingCharacterEquiv_symm_points, productEmbeddingCharacterEquiv_symm_points]
  calc
    _ = ∏ j, productEmbeddingPointsEquiv k L E T x
          (productEmbeddingPermutation k L E σ j) ^ m j := by
      apply Finset.prod_congr rfl
      intro j _
      rw [productEmbeddingPointsEquiv_descentPoint]
    _ = _ := by
      rw [← Equiv.prod_comp (productEmbeddingPermutation k L E σ)
        (fun j => productEmbeddingPointsEquiv k L E T x j ^
          m ⟨j.1, σ.symm.toAlgHom.comp j.2⟩)]
      apply Finset.prod_congr rfl
      intro j _
      congr 1
      symm
      change m ((productEmbeddingPermutation k L E σ).symm
        (productEmbeddingPermutation k L E σ j)) = m j
      rw [Equiv.symm_apply_apply]

/-- The coordinate equivalence intertwines the actual character Galois action. -/
theorem productEmbeddingCharacterEquiv_galoisRepresentation
    (σ : L ≃ₐ[k] L) (χ : characterLattice W_L) :
    productEmbeddingCharacterEquiv k L E
        (characterLattice.galoisRepresentation k L
          (commGroupScheme (CommRingCat.of k) (∀ i, E i)) σ χ) =
      fun j => productEmbeddingCharacterEquiv k L E χ
        ⟨j.1, σ.symm.toAlgHom.comp j.2⟩ := by
  conv_lhs => rw [← (productEmbeddingCharacterEquiv k L E).symm_apply_apply χ]
  rw [galoisRepresentation_productEmbeddingCharacterEquiv_symm, AddEquiv.apply_symm_apply]

end Langlands.GroupScheme.WeilGm
