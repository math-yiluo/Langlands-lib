import Langlands.Algebra.BrauerCorestriction.CentralSimple
import Langlands.Algebra.BrauerCorestriction.Functoriality

/-!
# Tensor descent of split algebras

Let `φ : A →ₐ[L] End_L(W)` be a representation of an `L`-algebra `A` on an `L`-algebra `W`
(used only as a vector space). Factorwise, the conjugates `A^σ` act on the conjugates `W^σ`,
so `⨂_σ A^σ` acts `N`-linearly on `⨂_σ W^σ`, compatibly with the Galois actions. Hence the
descended algebra of `A` acts `K`-linearly on the descended space of `W`. When `A` is central
simple of dimension `(dim W)^2`, this action is an isomorphism `corAlg A ≃ End_K(corAlg W)`. In
particular the descended algebra of `M_n(L)` is a full matrix algebra over `K`.
-/

universe u₁ u₂ u₃ u₄ u₅

open TensorProduct PiTensorProduct Module
open Langlands.PiTensorSemilinear

namespace Langlands.BrauerCorestriction

section Action

variable {K : Type u₁} {L : Type u₂} {N : Type u₃} [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable {A : Type u₄} [Ring A] [Algebra L A] {W : Type u₅} [Ring W] [Algebra L W]

/-- The action of `A^σ` on `W^σ`, as a `Twist σ`-algebra homomorphism. -/
noncomputable def conjActTwist (φ : A →ₐ[L] Module.End L W) (σ : L →ₐ[K] N) :
    Conj A σ →ₐ[Twist σ] Module.End (Twist σ) (Conj W σ) :=
  Algebra.TensorProduct.lift (Algebra.ofId (Twist σ) _)
    ((Module.End.baseChangeHom L (Twist σ) W).comp φ) (fun x _ => Algebra.commutes x _)

/-- The action of `A^σ` on `W^σ` by `N`-linear endomorphisms. -/
noncomputable def conjAct (φ : A →ₐ[L] Module.End L W) (σ : L →ₐ[K] N) :
    Conj A σ →ₗ[N] Module.End N (Conj W σ) where
  toFun c := (conjActTwist φ σ c).restrictScalars N
  map_add' c d := by rw [map_add]; rfl
  map_smul' n c := by
    ext v
    exact congrArg (fun F : Module.End (Twist σ) (Conj W σ) => F v)
      (map_smul (conjActTwist φ σ) (show Twist σ from n) c)

theorem conjAct_tmul_tmul (φ : A →ₐ[L] Module.End L W) (σ : L →ₐ[K] N) (x y : Twist σ)
    (a : A) (w : W) :
    conjAct φ σ (x ⊗ₜ a) (y ⊗ₜ w) = (x * y) ⊗ₜ φ a w := by
  change (algebraMap (Twist σ) (Module.End (Twist σ) (Conj W σ)) x)
    (((φ a).baseChange (Twist σ)) (y ⊗ₜ w)) = _
  rw [LinearMap.baseChange_tmul, Module.algebraMap_end_apply, smul_tmul', smul_eq_mul]

theorem conjAct_one (φ : A →ₐ[L] Module.End L W) (σ : L →ₐ[K] N) : conjAct φ σ 1 = 1 := by
  change (conjActTwist φ σ 1).restrictScalars N = 1
  rw [map_one]
  rfl

theorem conjAct_mul (φ : A →ₐ[L] Module.End L W) (σ : L →ₐ[K] N) (c d : Conj A σ) :
    conjAct φ σ (c * d) = conjAct φ σ c * conjAct φ σ d := by
  change (conjActTwist φ σ (c * d)).restrictScalars N = _
  rw [map_mul]
  rfl

/-- The action is compatible with Galois conjugation. -/
theorem conjMap_conjAct (φ : A →ₐ[L] Module.End L W) (g : N ≃ₐ[K] N) (σ τ : L →ₐ[K] N)
    (h : ∀ l, g (σ l) = τ l) (c : Conj A σ) (v : Conj W σ) :
    conjMap W g σ τ h (conjAct φ σ c v) =
      conjAct φ τ (conjMap A g σ τ h c) (conjMap W g σ τ h v) := by
  induction c using TensorProduct.inductionOn with
  | tmul x a =>
    induction v using TensorProduct.inductionOn with
    | tmul y w =>
      rw [conjAct_tmul_tmul, conjMap_tmul, conjMap_tmul, conjMap_tmul, conjAct_tmul_tmul,
        map_mul]
    | add v₁ v₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  | add c₁ c₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, map_add, h₁, h₂, map_add, map_add, LinearMap.add_apply]

variable (K L N) in
/-- The action of `⨂_σ A^σ` on `⨂_σ W^σ`, an `N`-algebra homomorphism. -/
noncomputable def tensorAct (φ : A →ₐ[L] Module.End L W) :
    ConjTensor K L N A →ₐ[N] Module.End N (ConjTensor K L N W) :=
  liftAlgHom ((mapMultilinear N (fun σ : L →ₐ[K] N => Conj W σ)
      (fun σ : L →ₐ[K] N => Conj W σ)).compLinearMap (fun σ => conjAct φ σ))
    (by
      simp only [MultilinearMap.compLinearMap_apply, mapMultilinear_apply, Pi.one_apply,
        conjAct_one]
      exact PiTensorProduct.map_one)
    (fun x y => by
      simp only [MultilinearMap.compLinearMap_apply, mapMultilinear_apply, Pi.mul_apply,
        conjAct_mul]
      exact PiTensorProduct.map_mul _ _)

theorem tensorAct_tprod_tprod (φ : A →ₐ[L] Module.End L W) (c : ∀ σ : L →ₐ[K] N, Conj A σ)
    (v : ∀ σ : L →ₐ[K] N, Conj W σ) :
    tensorAct K L N φ (PiTensorProduct.tprod N c) (PiTensorProduct.tprod N v) =
      PiTensorProduct.tprod N (fun σ => conjAct φ σ (c σ) (v σ)) := by
  simp [tensorAct]

theorem actMap_tensorAct_tprod (φ : A →ₐ[L] Module.End L W) (g : N ≃ₐ[K] N)
    (c : ∀ σ : L →ₐ[K] N, Conj A σ) (y : ∀ σ : L →ₐ[K] N, Conj W σ) :
    actMap W g (tensorAct K L N φ (PiTensorProduct.tprod N c) (PiTensorProduct.tprod N y)) =
      tensorAct K L N φ (actMap A g (PiTensorProduct.tprod N c))
        (actMap W g (PiTensorProduct.tprod N y)) := by
  rw [tensorAct_tprod_tprod, actMap_tprod, actMap_tprod, actMap_tprod, tensorAct_tprod_tprod]
  congr 1
  funext τ
  exact conjMap_conjAct φ g _ τ _ _ _

/-- The action intertwines the Galois actions. -/
theorem actMap_tensorAct (φ : A →ₐ[L] Module.End L W) (g : N ≃ₐ[K] N)
    (t : ConjTensor K L N A) (v : ConjTensor K L N W) :
    actMap W g (tensorAct K L N φ t v) = tensorAct K L N φ (actMap A g t) (actMap W g v) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r c =>
    induction v using PiTensorProduct.induction_on with
    | smul_tprod s y =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, actMap_tensorAct_tprod]
    | add v₁ v₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, map_add, h₁, h₂, map_add, map_add, LinearMap.add_apply]

theorem tensorAct_mem_corAlg (φ : A →ₐ[L] Module.End L W) {t : ConjTensor K L N A}
    (ht : t ∈ corAlg K L N A) {v : ConjTensor K L N W} (hv : v ∈ corAlg K L N W) :
    tensorAct K L N φ t v ∈ corAlg K L N W := by
  rw [mem_corAlg] at ht hv ⊢
  intro g
  rw [actMap_tensorAct, ht g, hv g]

theorem tensorAct_smul_K (φ : A →ₐ[L] Module.End L W) (t : ConjTensor K L N A) (k : K)
    (v : ConjTensor K L N W) :
    tensorAct K L N φ t (k • v) = k • tensorAct K L N φ t v := by
  rw [← algebraMap_smul N k v, map_smul, algebraMap_smul]

variable (K L N) in
/-- The descended action: `corAlg A` acts `K`-linearly on `corAlg W`. -/
noncomputable def corAct (φ : A →ₐ[L] Module.End L W) :
    corAlg K L N A →ₐ[K] Module.End K (corAlg K L N W) where
  toFun d :=
    { toFun := fun v => ⟨tensorAct K L N φ d v, tensorAct_mem_corAlg φ d.2 v.2⟩
      map_add' := fun v w => by
        apply Subtype.ext
        simp only [AddMemClass.coe_add]
        exact map_add _ (v : ConjTensor K L N W) (w : ConjTensor K L N W)
      map_smul' := fun k v => by
        apply Subtype.ext
        simp only [SetLike.val_smul, RingHom.id_apply]
        exact tensorAct_smul_K φ d k (v : ConjTensor K L N W) }
  map_one' := by
    ext v
    simp only [OneMemClass.coe_one, LinearMap.coe_mk, AddHom.coe_mk, map_one,
      Module.End.one_apply, Subtype.coe_eta]
  map_mul' d e := by
    ext v
    simp only [MulMemClass.coe_mul, map_mul, LinearMap.coe_mk, AddHom.coe_mk,
      Module.End.mul_apply]
  map_zero' := by
    ext v
    simp only [ZeroMemClass.coe_zero, map_zero, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.zero_apply]
  map_add' d e := by
    ext v
    simp only [AddMemClass.coe_add, map_add, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply]
  commutes' k := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.algebraMap_end_apply,
      SetLike.val_smul]
    change tensorAct K L N φ (algebraMap K (ConjTensor K L N A) k) v = k • (v : ConjTensor K L N W)
    rw [IsScalarTower.algebraMap_apply K N, AlgHom.commutes, Module.algebraMap_end_apply,
      algebraMap_smul]

@[simp]
theorem corAct_apply (φ : A →ₐ[L] Module.End L W) (d : corAlg K L N A) (v : corAlg K L N W) :
    (corAct K L N φ d v : ConjTensor K L N W) = tensorAct K L N φ d v := rfl

end Action

section Bijective

variable (K : Type u₁) (L : Type u₂) (N : Type u₃) [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable {A : Type u₄} [Ring A] [Algebra L A] {W : Type u₅} [Ring W] [Algebra L W]
variable [FiniteDimensional K L] [FiniteDimensional K N] [IsGalois K N]
  [FiniteDimensional L A] [Algebra.IsCentral L A] [IsSimpleRing A] [FiniteDimensional L W]

/-- The descended action in coordinates: a `K`-algebra homomorphism from `corAlg A` to square
matrices of size `dim_K (corAlg W)`. -/
noncomputable def corActMatrix (φ : A →ₐ[L] Module.End L W) :
    corAlg K L N A →ₐ[K]
      Matrix (Fin (finrank K (corAlg K L N W))) (Fin (finrank K (corAlg K L N W))) K :=
  have : FiniteDimensional K (corAlg K L N W) := finiteDimensional_corAlg K L N W
  have : Module.Free K (corAlg K L N W) :=
    @Module.Free.of_divisionRing K (corAlg K L N W) _ inferInstance inferInstance
  (LinearMap.toMatrixAlgEquiv (Module.finBasis K (corAlg K L N W))).toAlgHom.comp
    (corAct K L N φ)

/-- If `A` is central simple of dimension `(dim W)^2`, the descended action is bijective. -/
theorem corActMatrix_bijective [Nontrivial W] (φ : A →ₐ[L] Module.End L W)
    (hdim : finrank L A = finrank L W ^ 2) : Function.Bijective (corActMatrix K L N φ) := by
  have : IsSimpleRing (corAlg K L N A) := isSimpleRing_corAlg K L N A
  have : FiniteDimensional K (corAlg K L N A) := finiteDimensional_corAlg K L N A
  have hW : 0 < finrank K (corAlg K L N W) := by
    rw [finrank_corAlg_eq_pow]
    exact pow_pos Module.finrank_pos _
  have : NeZero (finrank K (corAlg K L N W)) := ⟨hW.ne'⟩
  have hinj : Function.Injective (corActMatrix K L N φ) := by
    rcases IsSimpleRing.injective_ringHom_or_subsingleton_codomain (R := corAlg K L N A)
      (S := Matrix (Fin (finrank K (corAlg K L N W))) (Fin (finrank K (corAlg K L N W))) K)
      (corActMatrix K L N φ).toRingHom with h | h
    · exact h
    · exact absurd h (not_subsingleton _)
  refine ⟨hinj, ?_⟩
  have hd : finrank K (corAlg K L N A) =
      finrank K (Matrix (Fin (finrank K (corAlg K L N W)))
        (Fin (finrank K (corAlg K L N W))) K) := by
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one,
      finrank_corAlg_eq_pow, finrank_corAlg_eq_pow, hdim, ← pow_mul, ← mul_pow, ← sq, ← pow_mul,
      mul_comm]
  let f : corAlg K L N A →ₗ[K]
      Matrix (Fin (finrank K (corAlg K L N W))) (Fin (finrank K (corAlg K L N W))) K :=
    { toFun := corActMatrix K L N φ
      map_add' := map_add _
      map_smul' := fun c x => map_smul (corActMatrix K L N φ) c x }
  have key := LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := K)
    (V := corAlg K L N A)
    (V₂ := Matrix (Fin (finrank K (corAlg K L N W))) (Fin (finrank K (corAlg K L N W))) K)
    (f := f) hd
  exact key.mp hinj

/-- The descended algebra of `A` is a full matrix algebra over `K`, of size `dim_K corAlg W`. -/
noncomputable def corAlgMatrixEquivOfRep [Nontrivial W] (φ : A →ₐ[L] Module.End L W)
    (hdim : finrank L A = finrank L W ^ 2) :
    corAlg K L N A ≃ₐ[K]
      Matrix (Fin (finrank K (corAlg K L N W))) (Fin (finrank K (corAlg K L N W))) K :=
  AlgEquiv.ofBijective (corActMatrix K L N φ) (corActMatrix_bijective K L N φ hdim)

end Bijective

section Matrix

variable (K : Type u₁) (L : Type u₂) (N : Type u₃) [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable [FiniteDimensional K L] [FiniteDimensional K N] [IsGalois K N]
variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem finrank_corAlg_fin_fun :
    finrank K (corAlg K L N (Fin n → L)) = n ^ Nat.card (L →ₐ[K] N) := by
  rw [finrank_corAlg_eq_pow, Module.finrank_fin_fun]

/-- The tensor descent of `M_n(L)` is a full matrix algebra over `K` of size
`n ^ #(L →ₐ[K] N)`. -/
noncomputable def corAlgMatrixEquiv :
    corAlg K L N (Matrix (Fin n) (Fin n) L) ≃ₐ[K]
      Matrix (Fin (n ^ Nat.card (L →ₐ[K] N))) (Fin (n ^ Nat.card (L →ₐ[K] N))) K :=
  (corAlgMatrixEquivOfRep K L N
      (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) L ≃ₐ[L] _).toAlgHom
      (by rw [Module.finrank_matrix, Module.finrank_fin_fun, Module.finrank_self, mul_one,
        Fintype.card_fin, sq])).trans
    (Matrix.reindexAlgEquiv K K (finCongr (finrank_corAlg_fin_fun K L N n)))

end Matrix

end Langlands.BrauerCorestriction
