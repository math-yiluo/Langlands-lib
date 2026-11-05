import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints
import Langlands.GroupScheme.Torus.WeilRestrictionSeparable
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Embedding coordinates for norms on products of Weil restrictions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.Algebra.SeparableTensor

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

attribute [local instance] Classical.propDecidable

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]

omit [FiniteDimensional k L] in
/-- Intermediate-field minimal polynomials split in the given normal extension. -/
theorem intermediate_minpoly_splits (E : IntermediateField k L) (x : E) :
    ((minpoly k x).map (algebraMap k L)).Splits := by
  rw [← minpoly.algHom_eq E.val E.val.injective x]
  exact (inferInstance : Normal k L).splits (x : L)

variable {I : Type u} [Fintype I] [DecidableEq I]
  (E : I → IntermediateField k L)

/-- The tensor algebra of a finite product of intermediate fields in embedding coordinates. -/
def productTensorEmbeddingEquiv :
    (∀ i, E i) ⊗[k] L ≃+* (∀ i, (E i →ₐ[k] L) → L) :=
  (Algebra.TensorProduct.comm k (∀ i, E i) L).toRingEquiv.trans
    (((Algebra.TensorProduct.piRight k L L (fun i => E i)).trans
      (AlgEquiv.piCongrRight (fun i =>
        separableEmbeddingDecomposition k (E i) L
          (intermediate_minpoly_splits k L (E i))))).toRingEquiv)

@[simp] theorem productTensorEmbeddingEquiv_tmul (a : ∀ i, E i) (c : L)
    (i : I) (τ : E i →ₐ[k] L) :
    productTensorEmbeddingEquiv k L E (a ⊗ₜ c) i τ = τ (a i) * c := by
  change c * τ (a i) = τ (a i) * c
  exact mul_comm _ _

/-- The same product decomposition on units. -/
def productTensorEmbeddingUnitsEquiv :
    ((∀ i, E i) ⊗[k] L)ˣ ≃* (∀ i, (E i →ₐ[k] L) → Lˣ) :=
  (Units.mapEquiv (productTensorEmbeddingEquiv k L E).toMulEquiv).trans
    (MulEquiv.piUnits.trans (MulEquiv.piCongrRight fun _ => MulEquiv.piUnits))

/-- Coefficient conjugation acts semilinearly and permutes the embeddings. -/
theorem productTensorEmbeddingEquiv_conjugate (σ : L ≃ₐ[k] L)
    (x : (∀ i, E i) ⊗[k] L) (i : I) (τ : E i →ₐ[k] L) :
    productTensorEmbeddingEquiv k L E
        (Algebra.TensorProduct.lTensor (S := (∀ i, E i)) (∀ i, E i) σ.toAlgHom x) i τ =
      σ (productTensorEmbeddingEquiv k L E x i (σ.symm.toAlgHom.comp τ)) := by
  induction x using TensorProduct.inductionOn with
  | tmul a c => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- A conjugate can contribute to a single inclusion coordinate exactly when it fixes E. -/
theorem inverse_comp_val_eq_iff (E : IntermediateField k L) (σ : L ≃ₐ[k] L) :
    σ.symm.toAlgHom.comp E.val = E.val ↔ σ ∈ E.fixingSubgroup := by
  constructor
  · intro h
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h' := DFunLike.congr_fun h (⟨x, hx⟩ : E)
    change σ.symm x = x at h'
    exact (congrArg σ h').symm.trans (σ.apply_symm_apply x)
  · intro h
    ext x
    apply σ.injective
    simpa using ((IntermediateField.mem_fixingSubgroup_iff E σ).mp h x x.property).symm

/-- The coefficient product supported at the inclusion is the relative field norm. -/
theorem prod_automorphisms_single (E : IntermediateField k L) (b : L) :
    (∏ σ : L ≃ₐ[k] L,
      if σ.symm.toAlgHom.comp E.val = E.val then σ b else 1) =
        algebraMap E L (Algebra.norm E b) := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  calc
    _ = ∏ σ : E.fixingSubgroup, (σ : L ≃ₐ[k] L) b := by
      apply Finset.prod_congr_set (E.fixingSubgroup : Set (L ≃ₐ[k] L))
      · intro σ hσ
        rw [ite_eq_left ((inverse_comp_val_eq_iff k L E σ).mpr hσ)]
      · intro σ hσ
        rw [ite_eq_right (fun h => hσ ((inverse_comp_val_eq_iff k L E σ).mp h))]
    _ = ∏ σ : L ≃ₐ[E] L, σ b :=
      Fintype.prod_equiv (IntermediateField.fixingSubgroupEquiv E).toEquiv _ _ (fun _ => rfl)

end Langlands.GroupScheme.WeilGm
