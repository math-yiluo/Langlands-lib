import Langlands.Automorphic.ArchimedeanResidualMultiplicity

/-! # Retaining nonzero local components after tensor separation -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.TensorContraction

open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe uA uB uW uQ uK uL

variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
  {B : Type uB} [AddCommGroup B] [Module ℂ B]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Q : Type uQ} [AddCommGroup Q] [Module ℂ Q]

/-- Contract the first tensor factor against a complex-linear functional. -/
def contract (φ : A →ₗ[ℂ] ℂ) : A ⊗[ℂ] B →ₗ[ℂ] B :=
  (TensorProduct.lid ℂ B).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id

@[simp]
theorem contract_tmul (φ : A →ₗ[ℂ] ℂ) (a : A) (b : B) :
    contract φ (a ⊗ₜ[ℂ] b) = φ a • b := rfl

theorem contract_second (φ : A →ₗ[ℂ] ℂ) (T : Module.End ℂ B) (t : A ⊗[ℂ] B) :
    contract φ (TensorProduct.map LinearMap.id T t) = T (contract φ t) := by
  induction t with
  | tmul a b => exact (T.map_smul (φ a) b).symm
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- Some first-factor contraction detects every nonzero tensor. -/
theorem exists_contract_ne_zero {t : A ⊗[ℂ] B} (ht : t ≠ 0) :
    ∃ φ : A →ₗ[ℂ] ℂ, contract φ t ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ A
  have heq (i) : contract (b.coord i) t = TensorProduct.equivFinsuppOfBasisLeft b t i := by
    clear ht
    induction t with
    | tmul a c =>
      simp only [contract_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        Module.Basis.coord_apply]
    | add t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht']
  obtain ⟨i, hi⟩ : ∃ i, TensorProduct.equivFinsuppOfBasisLeft b t i ≠ 0 := by
    by_contra h
    apply ht
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    exact (Finsupp.ext fun i => not_not.mp (not_exists.mp h i)).trans (map_zero _).symm
  exact ⟨b.coord i, heq i ▸ hi⟩

/-- A coordinate projection onto the residual factor of a tensor equivalence. -/
def contractEquiv (e : A ⊗[ℂ] B ≃ₗ[ℂ] W) (φ : A →ₗ[ℂ] ℂ) : W →ₗ[ℂ] B :=
  (contract φ).comp e.symm.toLinearMap

theorem contractEquiv_intertwines (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
    (φ : A →ₗ[ℂ] ℂ) (T : Module.End ℂ W) (U : Module.End ℂ B)
    (he : ∀ t, e (TensorProduct.map LinearMap.id U t) = T (e t)) (w : W) :
    contractEquiv e φ (T w) = U (contractEquiv e φ w) := by
  obtain ⟨t, rfl⟩ := e.surjective w
  change contract φ (e.symm (T (e t))) = U (contract φ (e.symm (e t)))
  rw [← he, e.symm_apply_apply, e.symm_apply_apply]
  exact contract_second φ U t

/-- A nonzero map into the original target remains nonzero after some contraction. -/
theorem exists_nonzero_contraction (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
    (j : Q →ₗ[ℂ] W) (hj : j ≠ 0) :
    ∃ φ : A →ₗ[ℂ] ℂ, (contractEquiv e φ).comp j ≠ 0 := by
  obtain ⟨q, hq⟩ : ∃ q, j q ≠ 0 := by
    by_contra h
    exact hj (LinearMap.ext fun q => not_not.mp (not_exists.mp h q))
  have ht : e.symm (j q) ≠ 0 := fun h =>
    hq (e.symm.injective (h.trans (map_zero e.symm).symm))
  obtain ⟨φ, hφ⟩ := exists_contract_ne_zero ht
  refine ⟨φ, fun hzero => hφ ?_⟩
  exact LinearMap.congr_fun hzero q

variable {K : Type uK} [Group K] {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  (σ : Representation ℂ K Q) (p : L →ₗ⁅ℂ⁆ Module.End ℂ Q)
  (ρB : Representation ℂ K B) (πB : L →ₗ⁅ℂ⁆ Module.End ℂ B)
  (ρW : Representation ℂ K W) (πW : L →ₗ⁅ℂ⁆ Module.End ℂ W)
  (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
  (hek : ∀ k t, e (TensorProduct.map LinearMap.id (ρB k) t) = ρW k (e t))
  (hel : ∀ X t, e (TensorProduct.map LinearMap.id (πB X) t) = πW X (e t))

/-- Contract a simultaneous local intertwiner into the residual factor, retaining
both its compact and its Lie covariance. -/
def contractedGKHom (φ : A →ₗ[ℂ] ℂ) (f : gkHoms σ p ρW πW) : gkHoms σ p ρB πB :=
  ⟨(contractEquiv e φ).comp f.val,
    fun k q => (congrArg (contractEquiv e φ) (f.property.1 k q)).trans
      (contractEquiv_intertwines e φ (ρW k) (ρB k) (hek k) (f.val q)),
    fun X q => (congrArg (contractEquiv e φ) (f.property.2 X q)).trans
      (contractEquiv_intertwines e φ (πW X) (πB X) (hel X) (f.val q))⟩

/-- Every other nonzero local component survives removal of the first tensor factor. -/
theorem exists_nonzero_contractedGKHom (f : gkHoms σ p ρW πW) (hf : f ≠ 0) :
    ∃ φ : A →ₗ[ℂ] ℂ, contractedGKHom σ p ρB πB ρW πW e hek hel φ f ≠ 0 := by
  have hf' : f.val ≠ 0 := fun h => hf (Subtype.ext h)
  obtain ⟨φ, hφ⟩ := exists_nonzero_contraction e f.val hf'
  refine ⟨φ, fun hzero => hφ ?_⟩
  exact congrArg Subtype.val hzero

end Langlands.Archimedean.TensorContraction
