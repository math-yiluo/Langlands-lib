import Langlands.Algebra.BrauerCorestriction.CentralSimple

/-!
# Kronecker identification of a finite tensor power of matrix algebras

For a field `F`, a finite type `E` and `m ≠ 0`, the `E`-fold tensor power of `M_m(F)` is
identified with the matrix algebra indexed by functions `E → Fin m`, by
`⨂_σ A_σ ↦ ((i, j) ↦ ∏_σ A_σ (i σ) (j σ))`. Under this identification reindexing the tensor
factors along a permutation of `E` becomes reindexing rows and columns, and applying a field
automorphism to all entries is compatible on both sides.
-/

universe u₁ u₂

open TensorProduct PiTensorProduct Module

namespace Langlands.BrauerCorestriction

variable (F : Type u₁) [Field F] (E : Type u₂) [Fintype E] [DecidableEq E] (m : ℕ)

/-- The Kronecker multilinear map `(A_σ)_σ ↦ ((i, j) ↦ ∏_σ A_σ (i σ) (j σ))`. -/
def kroneckerMultilinear :
    MultilinearMap F (fun _ : E => Matrix (Fin m) (Fin m) F)
      (Matrix (E → Fin m) (E → Fin m) F) where
  toFun A := Matrix.of fun i j => ∏ σ, A σ (i σ) (j σ)
  map_update_add' A σ X Y := by
    ext i j
    have key : ∀ Z : Matrix (Fin m) (Fin m) F,
        (∏ τ, (Function.update A σ Z τ) (i τ) (j τ)) =
          Z (i σ) (j σ) * ∏ τ ∈ Finset.univ \ {σ}, A τ (i τ) (j τ) := by
      intro Z
      rw [show (fun τ => (Function.update A σ Z τ) (i τ) (j τ)) =
          Function.update (fun τ => A τ (i τ) (j τ)) σ (Z (i σ) (j σ)) from
        funext fun τ => Function.apply_update
          (fun τ (M : Matrix (Fin m) (Fin m) F) => M (i τ) (j τ)) A σ Z τ]
      exact Finset.prod_update_of_mem (Finset.mem_univ σ) _ _
    simp only [Matrix.of_apply, Matrix.add_apply, key, add_mul]
  map_update_smul' A σ c X := by
    ext i j
    have key : ∀ Z : Matrix (Fin m) (Fin m) F,
        (∏ τ, (Function.update A σ Z τ) (i τ) (j τ)) =
          Z (i σ) (j σ) * ∏ τ ∈ Finset.univ \ {σ}, A τ (i τ) (j τ) := by
      intro Z
      rw [show (fun τ => (Function.update A σ Z τ) (i τ) (j τ)) =
          Function.update (fun τ => A τ (i τ) (j τ)) σ (Z (i σ) (j σ)) from
        funext fun τ => Function.apply_update
          (fun τ (M : Matrix (Fin m) (Fin m) F) => M (i τ) (j τ)) A σ Z τ]
      exact Finset.prod_update_of_mem (Finset.mem_univ σ) _ _
    simp only [Matrix.of_apply, Matrix.smul_apply, key, smul_eq_mul, mul_assoc]

omit [DecidableEq E] in
@[simp]
theorem kroneckerMultilinear_apply (A : E → Matrix (Fin m) (Fin m) F) (i j : E → Fin m) :
    kroneckerMultilinear F E m A i j = ∏ σ, A σ (i σ) (j σ) := rfl

omit [DecidableEq E] in
theorem kroneckerMultilinear_one :
    kroneckerMultilinear F E m 1 = 1 := by
  ext i j
  rw [kroneckerMultilinear_apply, Matrix.one_apply]
  simp only [Pi.one_apply, Matrix.one_apply]
  rw [Fintype.prod_boole]
  simp only [funext_iff]

theorem kroneckerMultilinear_mul (A B : E → Matrix (Fin m) (Fin m) F) :
    kroneckerMultilinear F E m (A * B) =
      kroneckerMultilinear F E m A * kroneckerMultilinear F E m B := by
  ext i j
  simp only [kroneckerMultilinear_apply, Pi.mul_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

/-- The Kronecker algebra homomorphism `⨂_σ M_m(F) → M_{E → Fin m}(F)`. -/
noncomputable def kroneckerHom :
    (⨂[F] _ : E, Matrix (Fin m) (Fin m) F) →ₐ[F] Matrix (E → Fin m) (E → Fin m) F :=
  liftAlgHom (kroneckerMultilinear F E m) (kroneckerMultilinear_one F E m)
    (kroneckerMultilinear_mul F E m)

@[simp]
theorem kroneckerHom_tprod (A : E → Matrix (Fin m) (Fin m) F) :
    kroneckerHom F E m (PiTensorProduct.tprod F A) = kroneckerMultilinear F E m A := by
  simp [kroneckerHom]

theorem finrank_piMatrix :
    finrank F (⨂[F] _ : E, Matrix (Fin m) (Fin m) F) = (m * m) ^ Fintype.card E := by
  classical
  let b : E → Basis (Fin m × Fin m) F (Matrix (Fin m) (Fin m) F) :=
    fun _ => Matrix.stdBasis F (Fin m) (Fin m)
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct b), Fintype.card_pi]
  simp

theorem kroneckerHom_bijective [NeZero m] : Function.Bijective (kroneckerHom F E m) := by
  have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  have hs := (piTensor_isCentral_isSimpleRing F (fun _ : E => Matrix (Fin m) (Fin m) F)).2
  have : Nonempty (E → Fin m) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  have hinj : Function.Injective (kroneckerHom F E m) := by
    rcases IsSimpleRing.injective_ringHom_or_subsingleton_codomain
      (R := ⨂[F] _ : E, Matrix (Fin m) (Fin m) F)
      (S := Matrix (E → Fin m) (E → Fin m) F) (kroneckerHom F E m).toRingHom with h | h
    · exact h
    · exact absurd h (not_subsingleton _)
  refine ⟨hinj, ?_⟩
  have hd : finrank F (⨂[F] _ : E, Matrix (Fin m) (Fin m) F) =
      finrank F (Matrix (E → Fin m) (E → Fin m) F) := by
    rw [finrank_piMatrix, Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fun,
      Fintype.card_fin, mul_pow]
  have : FiniteDimensional F (⨂[F] _ : E, Matrix (Fin m) (Fin m) F) := PiTensorProduct.finite
  have key := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := F)
    (V := ⨂[F] _ : E, Matrix (Fin m) (Fin m) F) (V₂ := Matrix (E → Fin m) (E → Fin m) F)
    (f := { toFun := kroneckerHom F E m
            map_add' := map_add _
            map_smul' := fun c x => map_smul (kroneckerHom F E m) c x }) hd
  exact key.mp hinj

/-- The Kronecker algebra isomorphism `⨂_σ M_m(F) ≃ M_{E → Fin m}(F)`. -/
noncomputable def kroneckerEquiv [NeZero m] :
    (⨂[F] _ : E, Matrix (Fin m) (Fin m) F) ≃ₐ[F] Matrix (E → Fin m) (E → Fin m) F :=
  AlgEquiv.ofBijective (kroneckerHom F E m) (kroneckerHom_bijective F E m)


section Permutation

variable {F E m}

/-- The bijection `i ↦ i ∘ π⁻¹` of index functions induced by a permutation `π` of `E`. -/
def indexPerm (π : Equiv.Perm E) : (E → Fin m) ≃ (E → Fin m) :=
  π.arrowCongr (Equiv.refl (Fin m))

omit [Fintype E] [DecidableEq E] in
@[simp]
theorem indexPerm_symm_apply (π : Equiv.Perm E) (i : E → Fin m) (σ : E) :
    (indexPerm π).symm i σ = i (π σ) := rfl

omit [DecidableEq E] in
/-- Reindexing the factors along `π` corresponds to reindexing rows and columns. -/
theorem kroneckerMultilinear_reindex (π : Equiv.Perm E) (A : E → Matrix (Fin m) (Fin m) F) :
    kroneckerMultilinear F E m (fun σ => A (π.symm σ)) =
      (kroneckerMultilinear F E m A).submatrix (indexPerm π).symm (indexPerm π).symm := by
  ext i j
  simp only [kroneckerMultilinear_apply, Matrix.submatrix_apply, indexPerm_symm_apply]
  exact (Fintype.prod_equiv π _ _ (fun τ => by simp)).symm

omit [DecidableEq E] in
/-- Applying a ring homomorphism to all entries commutes with the Kronecker map. -/
theorem kroneckerMultilinear_map {F' : Type*} [Field F'] (f : F →+* F')
    (A : E → Matrix (Fin m) (Fin m) F) :
    (kroneckerMultilinear F E m A).map f = kroneckerMultilinear F' E m (fun σ => (A σ).map f) := by
  ext i j
  simp [map_prod]

/-- The permutation matrix of a bijection of an index type, as a unit. -/
def permUnit {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι ≃ ι) : (Matrix ι ι F)ˣ where
  val := s.toPEquiv.toMatrix
  inv := s.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem permUnit_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι ≃ ι) (X : Matrix ι ι F) :
    (permUnit (F := F) s : Matrix ι ι F) * X * ((permUnit (F := F) s)⁻¹ : (Matrix ι ι F)ˣ) =
      X.submatrix s s := by
  change s.toPEquiv.toMatrix * X * s.symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix,
    Equiv.symm_symm]
  rfl

theorem permUnit_trans {ι : Type*} [Fintype ι] [DecidableEq ι] (s t : ι ≃ ι) :
    permUnit (F := F) (s.trans t) = permUnit s * permUnit t := by
  ext : 1
  change (s.trans t).toPEquiv.toMatrix = s.toPEquiv.toMatrix * t.toPEquiv.toMatrix
  rw [Equiv.toPEquiv_trans, PEquiv.toMatrix_trans]

theorem permUnit_map {ι : Type*} [Fintype ι] [DecidableEq ι] {F' : Type*} [Field F']
    (f : F →+* F') (s : ι ≃ ι) :
    (permUnit (F := F) s : Matrix ι ι F).map f = (permUnit (F := F') s : Matrix ι ι F') := by
  ext i j
  change f (s.toPEquiv.toMatrix i j) = s.toPEquiv.toMatrix i j
  rw [PEquiv.toMatrix_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

end Permutation

end Langlands.BrauerCorestriction
