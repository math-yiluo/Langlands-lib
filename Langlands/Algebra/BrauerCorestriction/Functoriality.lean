import Langlands.Algebra.BrauerCorestriction.Construction

/-!
# Functoriality of the tensor descent

An `L`-algebra homomorphism `f : A → B` induces Galois-equivariant `N`-algebra maps of the tensor
products of conjugates, hence `K`-algebra homomorphisms of the descended algebras. Isomorphisms
induce isomorphisms. The images of `A` and `B` in the descended algebra of `A ⊗[L] B` commute,
which gives the comparison homomorphism `corAlg A ⊗[K] corAlg B → corAlg (A ⊗[L] B)`.
-/

universe u₁ u₂ u₃ u₄ u₅ u₆

open TensorProduct PiTensorProduct
open Langlands.PiTensorSemilinear

namespace Langlands.BrauerCorestriction

variable {K : Type u₁} {L : Type u₂} {N : Type u₃} [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable {A : Type u₄} {B : Type u₅} {C : Type u₆} [Ring A] [Algebra L A] [Ring B]
  [Algebra L B] [Ring C] [Algebra L C]

section Factor

/-- The map of conjugates `A^σ → B^σ`, `x ⊗ a ↦ x ⊗ f a`, as an `N`-linear map. -/
noncomputable def conjFun (f : A →ₐ[L] B) (σ : L →ₐ[K] N) : Conj A σ →ₗ[N] Conj B σ where
  toFun := Algebra.TensorProduct.map (AlgHom.id L (Twist σ)) f
  map_add' := map_add _
  map_smul' n c := by
    induction c using TensorProduct.inductionOn with
    | tmul x a =>
      rw [smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        smul_tmul']
      rfl
    | add c₁ c₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]

@[simp]
theorem conjFun_tmul (f : A →ₐ[L] B) (σ : L →ₐ[K] N) (x : Twist σ) (a : A) :
    conjFun f σ (x ⊗ₜ a) = x ⊗ₜ f a := rfl

theorem conjFun_one (f : A →ₐ[L] B) (σ : L →ₐ[K] N) : conjFun f σ 1 = 1 :=
  map_one (Algebra.TensorProduct.map (AlgHom.id L (Twist σ)) f)

theorem conjFun_mul (f : A →ₐ[L] B) (σ : L →ₐ[K] N) (x y : Conj A σ) :
    conjFun f σ (x * y) = conjFun f σ x * conjFun f σ y :=
  map_mul (Algebra.TensorProduct.map (AlgHom.id L (Twist σ)) f) x y

theorem conjFun_id_apply (σ : L →ₐ[K] N) (c : Conj A σ) : conjFun (AlgHom.id L A) σ c = c := by
  induction c using TensorProduct.inductionOn with
  | tmul x a => rfl
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂]

theorem conjFun_comp_apply (g : B →ₐ[L] C) (f : A →ₐ[L] B) (σ : L →ₐ[K] N) (c : Conj A σ) :
    conjFun (g.comp f) σ c = conjFun g σ (conjFun f σ c) := by
  induction c using TensorProduct.inductionOn with
  | tmul x a => rfl
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, map_add]

theorem conjMap_conjFun (f : A →ₐ[L] B) (g : N ≃ₐ[K] N) (σ τ : L →ₐ[K] N)
    (h : ∀ l, g (σ l) = τ l) (c : Conj A σ) :
    conjMap B g σ τ h (conjFun f σ c) = conjFun f τ (conjMap A g σ τ h c) := by
  induction c using TensorProduct.inductionOn with
  | tmul x a => rfl
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]

end Factor

section Tensor

variable (K L N) in
/-- The `N`-linear map `⨂_σ A^σ → ⨂_σ B^σ` induced by an `L`-algebra homomorphism. -/
noncomputable def funMap (f : A →ₐ[L] B) : ConjTensor K L N A →ₗ[N] ConjTensor K L N B :=
  piTensorSemilinear (RingHom.id N) (fun σ => conjFun f σ)

theorem funMap_tprod (f : A →ₐ[L] B) (x : ∀ σ : L →ₐ[K] N, Conj A σ) :
    funMap K L N f (PiTensorProduct.tprod N x) =
      PiTensorProduct.tprod N (fun σ => conjFun f σ (x σ)) :=
  piTensorSemilinear_tprod _ x

theorem funMap_one (f : A →ₐ[L] B) : funMap K L N f 1 = 1 :=
  piTensorSemilinear_one _ (fun σ => conjFun_one f σ)

theorem funMap_mul (f : A →ₐ[L] B) (x y : ConjTensor K L N A) :
    funMap K L N f (x * y) = funMap K L N f x * funMap K L N f y :=
  piTensorSemilinear_mul _ (fun σ => conjFun_mul f σ) x y

theorem funMap_id_apply (v : ConjTensor K L N A) : funMap K L N (AlgHom.id L A) v = v := by
  rw [funMap, piTensorSemilinear_id _ (fun σ c => conjFun_id_apply σ c), LinearMap.id_apply]

theorem funMap_comp_apply (g : B →ₐ[L] C) (f : A →ₐ[L] B) (v : ConjTensor K L N A) :
    funMap K L N (g.comp f) v = funMap K L N g (funMap K L N f v) := by
  rw [← LinearMap.comp_apply, funMap, funMap, funMap,
    piTensorSemilinear_comp _ _ _ (fun σ c => conjFun_comp_apply g f σ c)]

/-- The induced map commutes with the Galois actions. -/
theorem funMap_actMap (f : A →ₐ[L] B) (g : N ≃ₐ[K] N) (v : ConjTensor K L N A) :
    actMap B g (funMap K L N f v) = funMap K L N f (actMap A g v) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smulₛₗ, map_smulₛₗ, map_smul, funMap_tprod, actMap_tprod, actMap_tprod,
      funMap_tprod]
    congr 2
    funext τ
    exact conjMap_conjFun f g _ τ _ _
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]

theorem funMap_smul (f : A →ₐ[L] B) (k : K) (v : ConjTensor K L N A) :
    funMap K L N f (k • v) = k • funMap K L N f v := by
  rw [← algebraMap_smul N k v, map_smul, algebraMap_smul]

theorem funMap_mem_corAlg (f : A →ₐ[L] B) {v : ConjTensor K L N A}
    (hv : v ∈ corAlg K L N A) : funMap K L N f v ∈ corAlg K L N B := by
  rw [mem_corAlg] at hv ⊢
  intro g
  rw [funMap_actMap, hv g]

variable (K L N) in
/-- The `K`-algebra homomorphism of descended algebras induced by `f : A →ₐ[L] B`. -/
noncomputable def corFun (f : A →ₐ[L] B) : corAlg K L N A →ₐ[K] corAlg K L N B where
  toFun v := ⟨funMap K L N f v, funMap_mem_corAlg f v.2⟩
  map_one' := by
    apply Subtype.ext
    simp only [OneMemClass.coe_one]
    exact funMap_one f
  map_mul' x y := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    exact funMap_mul f (x : ConjTensor K L N A) (y : ConjTensor K L N A)
  map_zero' := by
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    exact map_zero _
  map_add' x y := by
    apply Subtype.ext
    simp only [AddMemClass.coe_add]
    exact map_add _ (x : ConjTensor K L N A) (y : ConjTensor K L N A)
  commutes' k := by
    apply Subtype.ext
    change funMap K L N f (algebraMap K _ k) = algebraMap K _ k
    rw [Algebra.algebraMap_eq_smul_one, funMap_smul, funMap_one, Algebra.algebraMap_eq_smul_one]

@[simp]
theorem corFun_apply (f : A →ₐ[L] B) (v : corAlg K L N A) :
    (corFun K L N f v : ConjTensor K L N B) = funMap K L N f v := rfl

variable (K L N) in
/-- An `L`-algebra isomorphism `A ≃ B` induces a `K`-algebra isomorphism of descended
algebras. -/
noncomputable def corEquiv (f : A ≃ₐ[L] B) : corAlg K L N A ≃ₐ[K] corAlg K L N B :=
  AlgEquiv.ofAlgHom (corFun K L N (f : A →ₐ[L] B)) (corFun K L N (f.symm : B →ₐ[L] A))
    (by
      ext v
      simp only [AlgHom.coe_comp, Function.comp_apply, corFun_apply, AlgHom.coe_id, id_eq]
      rw [← funMap_comp_apply]
      have : ((f : A →ₐ[L] B).comp (f.symm : B →ₐ[L] A)) = AlgHom.id L B := by
        ext b
        simp
      rw [this, funMap_id_apply])
    (by
      ext v
      simp only [AlgHom.coe_comp, Function.comp_apply, corFun_apply, AlgHom.coe_id, id_eq]
      rw [← funMap_comp_apply]
      have : ((f.symm : B →ₐ[L] A).comp (f : A →ₐ[L] B)) = AlgHom.id L A := by
        ext a
        simp
      rw [this, funMap_id_apply])

end Tensor

section Commute

open Algebra.TensorProduct in
theorem conjFun_includeLeft_commute (σ : L →ₐ[K] N) (c : Conj A σ) (d : Conj B σ) :
    Commute (conjFun (includeLeft : A →ₐ[L] A ⊗[L] B) σ c)
      (conjFun (includeRight : B →ₐ[L] A ⊗[L] B) σ d) := by
  induction c using TensorProduct.inductionOn with
  | tmul x a =>
    induction d using TensorProduct.inductionOn with
    | tmul y b =>
      simp only [conjFun_tmul, includeLeft_apply, includeRight_apply, Commute, SemiconjBy,
        tmul_mul_tmul, mul_one, one_mul]
      rw [mul_comm x y]
    | add d₁ d₂ h₁ h₂ => rw [map_add]; exact h₁.add_right h₂
  | add c₁ c₂ h₁ h₂ => rw [map_add]; exact h₁.add_left h₂

open Algebra.TensorProduct in
theorem funMap_includeLeft_commute (v : ConjTensor K L N A) (w : ConjTensor K L N B) :
    Commute (funMap K L N (includeLeft : A →ₐ[L] A ⊗[L] B) v)
      (funMap K L N (includeRight : B →ₐ[L] A ⊗[L] B) w) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    induction w using PiTensorProduct.induction_on with
    | smul_tprod s y =>
      rw [map_smul, map_smul, funMap_tprod, funMap_tprod]
      simp only [Commute, SemiconjBy]
      rw [smul_tprod_mul_smul_tprod, smul_tprod_mul_smul_tprod, mul_comm r s]
      congr 2
      funext σ
      exact (conjFun_includeLeft_commute σ (x σ) (y σ)).eq
    | add w₁ w₂ h₁ h₂ => rw [map_add]; exact h₁.add_right h₂
  | add v₁ v₂ h₁ h₂ => rw [map_add]; exact h₁.add_left h₂

variable (K L N A B) in
open Algebra.TensorProduct in
/-- The comparison homomorphism `corAlg A ⊗[K] corAlg B → corAlg (A ⊗[L] B)`. -/
noncomputable def corMul : corAlg K L N A ⊗[K] corAlg K L N B →ₐ[K] corAlg K L N (A ⊗[L] B) :=
  Algebra.TensorProduct.lift (corFun K L N (includeLeft : A →ₐ[L] A ⊗[L] B))
    (corFun K L N (includeRight : B →ₐ[L] A ⊗[L] B))
    (fun v w => by
      apply Subtype.ext
      exact funMap_includeLeft_commute (v : ConjTensor K L N A) (w : ConjTensor K L N B))

open Algebra.TensorProduct in
theorem corMul_tmul (v : corAlg K L N A) (w : corAlg K L N B) :
    (corMul K L N A B (v ⊗ₜ w) : ConjTensor K L N (A ⊗[L] B)) =
      funMap K L N (includeLeft : A →ₐ[L] A ⊗[L] B) v *
        funMap K L N (includeRight : B →ₐ[L] A ⊗[L] B) w := rfl

end Commute

end Langlands.BrauerCorestriction
