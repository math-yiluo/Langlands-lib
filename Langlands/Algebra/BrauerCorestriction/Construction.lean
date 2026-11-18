import Langlands.Algebra.BrauerCorestriction.GaloisDescent
import Langlands.Algebra.BrauerCorestriction.PiTensorSemilinear

/-!
# The tensor descent of conjugate algebras

Let `L/K` be a field extension, `N/K` a finite Galois extension and `A` an `L`-algebra. For each
`K`-embedding `σ : L → N` the conjugate `A^σ = N ⊗_{σ, L} A` is an `N`-algebra. The Galois group
`Gal(N/K)` acts on the tensor product `⨂_N σ, A^σ` by semilinear ring automorphisms permuting the
factors, and the fixed algebra is the tensor descent of the conjugates of `A`.
-/

universe u₁ u₂ u₃ u₄

open TensorProduct PiTensorProduct
open Langlands.PiTensorSemilinear

namespace Langlands.BrauerCorestriction

section Twist

variable {K : Type u₁} {L : Type u₂} {N : Type u₃} [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]

/-- The field `N` regarded as an `L`-algebra through the embedding `σ`. -/
@[nolint unusedArguments]
def Twist (_σ : L →ₐ[K] N) : Type u₃ := N

namespace Twist

variable (σ : L →ₐ[K] N)

instance : Field (Twist σ) := inferInstanceAs (Field N)

instance : Algebra N (Twist σ) := inferInstanceAs (Algebra N N)

instance : Algebra K (Twist σ) := inferInstanceAs (Algebra K N)

instance : IsScalarTower K N (Twist σ) := inferInstanceAs (IsScalarTower K N N)

instance : Algebra L (Twist σ) := RingHom.toAlgebra (σ : L →+* N)

theorem algebraMap_L_apply (l : L) : algebraMap L (Twist σ) l = (σ l : N) := rfl

theorem algebraMap_N_apply (x : N) : algebraMap N (Twist σ) x = (x : N) := rfl

instance : IsScalarTower K L (Twist σ) :=
  IsScalarTower.of_algebraMap_eq fun k => (σ.commutes k).symm

instance : SMulCommClass L N (Twist σ) :=
  ⟨fun l n x => by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _⟩

instance : SMulCommClass L K (Twist σ) :=
  ⟨fun l k x => by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _⟩

instance : Module.Finite N (Twist σ) := inferInstanceAs (Module.Finite N N)

end Twist

/-- The `L`-algebra map `Twist σ → Twist τ` given by a Galois automorphism `g` with
`g ∘ σ = τ`. -/
def twistHom (g : N ≃ₐ[K] N) (σ τ : L →ₐ[K] N) (h : ∀ l, g (σ l) = τ l) :
    Twist σ →ₐ[L] Twist τ :=
  { (g : N →+* N) with commutes' := h }

theorem twistHom_apply (g : N ≃ₐ[K] N) (σ τ : L →ₐ[K] N) (h : ∀ l, g (σ l) = τ l)
    (x : Twist σ) : twistHom g σ τ h x = (g (x : N) : N) := rfl

end Twist

section Conj

variable {K : Type u₁} {L : Type u₂} {N : Type u₃} [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable (A : Type u₄) [Ring A] [Algebra L A]

/-- The conjugate `A^σ = N ⊗_{σ, L} A`, an `N`-algebra. -/
abbrev Conj (σ : L →ₐ[K] N) : Type (max u₃ u₄) := Twist σ ⊗[L] A

/-- The conjugation map `A^σ → A^τ`, `x ⊗ a ↦ g x ⊗ a`, semilinear over `g`. -/
noncomputable def conjMap (g : N ≃ₐ[K] N) (σ τ : L →ₐ[K] N) (h : ∀ l, g (σ l) = τ l) :
    Conj A σ →ₛₗ[(g : N →+* N)] Conj A τ where
  toFun := Algebra.TensorProduct.map (twistHom g σ τ h) (AlgHom.id L A)
  map_add' := map_add _
  map_smul' n c := by
    induction c using TensorProduct.inductionOn with
    | tmul x a =>
      rw [smul_tmul']
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_tmul']
      congr 1
      exact map_mul g n x
    | add c₁ c₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]

variable {A}

@[simp]
theorem conjMap_tmul (g : N ≃ₐ[K] N) (σ τ : L →ₐ[K] N) (h : ∀ l, g (σ l) = τ l)
    (x : Twist σ) (a : A) :
    conjMap A g σ τ h (x ⊗ₜ a) = twistHom g σ τ h x ⊗ₜ a := rfl

theorem conjMap_one_apply (σ : L →ₐ[K] N) (h : ∀ l, (1 : N ≃ₐ[K] N) (σ l) = σ l)
    (c : Conj A σ) : conjMap A 1 σ σ h c = c := by
  induction c using TensorProduct.inductionOn with
  | tmul x a => rfl
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂]

theorem conjMap_conjMap (g g' : N ≃ₐ[K] N) (σ τ ρ : L →ₐ[K] N) (h : ∀ l, g' (σ l) = τ l)
    (h' : ∀ l, g (τ l) = ρ l) (h'' : ∀ l, (g * g') (σ l) = ρ l) (c : Conj A σ) :
    conjMap A g τ ρ h' (conjMap A g' σ τ h c) = conjMap A (g * g') σ ρ h'' c := by
  induction c using TensorProduct.inductionOn with
  | tmul x a => rfl
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]

theorem conjMap_one (g : N ≃ₐ[K] N) (σ τ : L →ₐ[K] N) (h : ∀ l, g (σ l) = τ l) :
    conjMap A g σ τ h 1 = 1 :=
  map_one (Algebra.TensorProduct.map (twistHom g σ τ h) (AlgHom.id L A))

theorem conjMap_mul (g : N ≃ₐ[K] N) (σ τ : L →ₐ[K] N) (h : ∀ l, g (σ l) = τ l)
    (x y : Conj A σ) : conjMap A g σ τ h (x * y) = conjMap A g σ τ h x * conjMap A g σ τ h y :=
  map_mul (Algebra.TensorProduct.map (twistHom g σ τ h) (AlgHom.id L A)) x y

end Conj

section Action

variable (K : Type u₁) (L : Type u₂) (N : Type u₃) [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N]
variable (A : Type u₄) [Ring A] [Algebra L A]

/-- The tensor product `⨂_N σ, A^σ` of all conjugates of `A`, over all `K`-embeddings
`σ : L → N`. -/
abbrev ConjTensor : Type (max u₂ u₃ u₄) := ⨂[N] σ : (L →ₐ[K] N), Conj A σ

variable {K L N}

/-- Left composition with a Galois automorphism permutes the `K`-embeddings `L → N`. -/
def galPerm (g : N ≃ₐ[K] N) : (L →ₐ[K] N) ≃ (L →ₐ[K] N) where
  toFun σ := (g : N →ₐ[K] N).comp σ
  invFun σ := (g.symm : N →ₐ[K] N).comp σ
  left_inv σ := by ext; simp
  right_inv σ := by ext; simp

@[simp]
theorem galPerm_apply_apply (g : N ≃ₐ[K] N) (σ : L →ₐ[K] N) (l : L) :
    galPerm g σ l = g (σ l) := rfl

@[simp]
theorem galPerm_symm_apply_apply (g : N ≃ₐ[K] N) (σ : L →ₐ[K] N) (l : L) :
    (galPerm g).symm σ l = g.symm (σ l) := rfl

theorem apply_galPerm_symm (g : N ≃ₐ[K] N) (τ : L →ₐ[K] N) (l : L) :
    g ((galPerm g).symm τ l) = τ l := by
  simp

/-- The semilinear action of `g` on `⨂_N σ, A^σ`: it sends the factor `A^σ` to `A^{gσ}` by
`conjMap`. -/
noncomputable def actMap (g : N ≃ₐ[K] N) :
    ConjTensor K L N A →ₛₗ[(g : N →+* N)] ConjTensor K L N A :=
  (piTensorSemilinear (g : N →+* N)
      (fun τ => conjMap A g ((galPerm g).symm τ) τ (apply_galPerm_symm g τ))).comp
    (reindex N (fun σ => Conj A σ) (galPerm g)).toLinearMap

variable {A}

theorem actMap_tprod (g : N ≃ₐ[K] N) (x : ∀ σ : L →ₐ[K] N, Conj A σ) :
    actMap A g (PiTensorProduct.tprod N x) = PiTensorProduct.tprod N (fun τ =>
      conjMap A g ((galPerm g).symm τ) τ (apply_galPerm_symm g τ) (x ((galPerm g).symm τ))) := by
  simp only [actMap, LinearMap.comp_apply, LinearEquiv.coe_coe, reindex_tprod,
    piTensorSemilinear_tprod]

/-- Pure tensors of conjugated factors depend only on the source-index function, not on the
proofs of compatibility. -/
theorem tprod_conjMap_congr (g : N ≃ₐ[K] N) {k₁ k₂ : (L →ₐ[K] N) → (L →ₐ[K] N)}
    (hk : k₁ = k₂) (h₁ : ∀ τ l, g (k₁ τ l) = τ l) (h₂ : ∀ τ l, g (k₂ τ l) = τ l)
    (x : ∀ σ : L →ₐ[K] N, Conj A σ) :
    PiTensorProduct.tprod N (fun τ => conjMap A g (k₁ τ) τ (h₁ τ) (x (k₁ τ))) =
      PiTensorProduct.tprod N (fun τ => conjMap A g (k₂ τ) τ (h₂ τ) (x (k₂ τ))) := by
  subst hk
  rfl

theorem actMap_one_apply (v : ConjTensor K L N A) : actMap A 1 v = v := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smulₛₗ, actMap_tprod]
    have hk : (fun τ : L →ₐ[K] N => (galPerm (1 : N ≃ₐ[K] N)).symm τ) = fun τ => τ := by
      funext τ
      ext l
      rfl
    rw [tprod_conjMap_congr 1 hk (fun τ => apply_galPerm_symm 1 τ)
      (fun τ l => AlgEquiv.one_apply _)]
    simp_rw [conjMap_one_apply]
    rfl
  | add v w hv hw => rw [map_add, hv, hw]

theorem actMap_mul_apply (g g' : N ≃ₐ[K] N) (v : ConjTensor K L N A) :
    actMap A (g * g') v = actMap A g (actMap A g' v) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, actMap_tprod, actMap_tprod, actMap_tprod]
    have hk : (fun τ : L →ₐ[K] N => (galPerm (g * g')).symm τ) =
        fun τ => (galPerm g').symm ((galPerm g).symm τ) := by
      funext τ
      ext l
      apply (g * g').injective
      simp [AlgEquiv.mul_apply]
    rw [tprod_conjMap_congr (g * g') hk (fun τ => apply_galPerm_symm (g * g') τ)
      (fun τ l => by simp [AlgEquiv.mul_apply])]
    refine congrArg₂ (· • ·) rfl (congrArg _ (funext fun τ => ?_))
    exact (conjMap_conjMap g g' _ _ τ _ _ _ _).symm
  | add v w hv hw => rw [map_add, hv, hw, map_add, map_add]

theorem actMap_one (g : N ≃ₐ[K] N) : actMap A g (1 : ConjTensor K L N A) = 1 := by
  simp only [actMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [reindex_one, piTensorSemilinear_one _ (fun τ => conjMap_one g _ τ _)]

theorem actMap_mul (g : N ≃ₐ[K] N) (x y : ConjTensor K L N A) :
    actMap A g (x * y) = actMap A g x * actMap A g y := by
  simp only [actMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [reindex_mul, piTensorSemilinear_mul _ (fun τ => conjMap_mul g _ τ _)]

variable (K L N A)

/-- The semilinear Galois action on `⨂_N σ, A^σ` by ring automorphisms permuting the factors. -/
noncomputable def galAction : GaloisDescent.SemilinearAlgAction K N (ConjTensor K L N A) where
  act g := (actMap A g).toAddMonoidHom
  one_act := actMap_one_apply
  mul_act := actMap_mul_apply
  act_smul g x v := map_smulₛₗ (actMap A g) x v
  act_one := actMap_one
  act_mul := actMap_mul

theorem galAction_act (g : N ≃ₐ[K] N) (v : ConjTensor K L N A) :
    (galAction K L N A).act g v = actMap A g v := rfl

/-- The tensor descent of the conjugates of `A`: the fixed `K`-subalgebra of the Galois action
on `⨂_N σ, A^σ`. -/
noncomputable abbrev corAlg : Subalgebra K (ConjTensor K L N A) :=
  (galAction K L N A).fixedSubalgebra

theorem mem_corAlg (v : ConjTensor K L N A) :
    v ∈ corAlg K L N A ↔ ∀ g : N ≃ₐ[K] N, actMap A g v = v := Iff.rfl

variable [FiniteDimensional K N] [IsGalois K N]

/-- Effective descent: scalar extension of the fixed algebra recovers `⨂_N σ, A^σ`. -/
noncomputable def corAlgEquiv : N ⊗[K] corAlg K L N A ≃ₐ[N] ConjTensor K L N A :=
  (galAction K L N A).descentAlgEquiv

@[simp]
theorem corAlgEquiv_tmul (x : N) (a : corAlg K L N A) :
    corAlgEquiv K L N A (x ⊗ₜ a) = x • (a : ConjTensor K L N A) :=
  GaloisDescent.SemilinearAlgAction.descentAlgEquiv_tmul _ x a

theorem finrank_corAlg :
    Module.finrank K (corAlg K L N A) = Module.finrank N (ConjTensor K L N A) :=
  (galAction K L N A).finrank_fixedSubalgebra

end Action

end Langlands.BrauerCorestriction
