import Langlands.Representation.Finite.VirtualCharacterProof
import Langlands.Representation.Tensor.Finite
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-! Characters and intertwining dimensions for external tensor products. -/

noncomputable section

open scoped BigOperators
open Representation

namespace Langlands.FiniteRep

variable {ι : Type} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)]

/-- The external tensor product of finite-dimensional complex representations. -/
def externalRep (V : ∀ i, FDRep ℂ (G i)) : FDRep ℂ (∀ i, G i) :=
  FDRep.of (FiniteTensor.external (fun i => (V i).ρ))

/-- Pull back a finite-dimensional representation along a group homomorphism. -/
def pullbackRep {H K : Type*} [Group H] [Group K] (f : H →* K) (V : FDRep ℂ K) : FDRep ℂ H :=
  FDRep.of (V.ρ.comp f)

@[simp] theorem character_pullbackRep {H K : Type*} [Group H] [Group K] (f : H →* K)
    (V : FDRep ℂ K) (g : H) : (pullbackRep f V).character g = V.character (f g) := rfl

/-- The external tensor character is the product of the component characters. -/
theorem character_externalRep (V : ∀ i, FDRep ℂ (G i)) (g : ∀ i, G i) :
    (externalRep V).character g = ∏ i, (V i).character (g i) := by
  classical
  let b (i : ι) := Module.finBasis ℂ (V i)
  change LinearMap.trace ℂ _ (FiniteTensor.external (fun i => (V i).ρ) g) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (Basis.piTensorProduct b)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
    FiniteTensor.external_tprod, Basis.piTensorProduct_repr_tprod_apply]
  rw [← Fintype.prod_sum (fun (i : ι) (j : Fin (Module.finrank ℂ (V i))) =>
    (b i).repr ((V i).ρ (g i) (b i j)) j)]
  apply Finset.prod_congr rfl
  intro i _
  change _ = LinearMap.trace ℂ (V i) ((V i).ρ (g i))
  rw [LinearMap.trace_eq_matrix_trace ℂ (b i)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]

private theorem isUnit_card_complex (H : Type*) [Group H] [Finite H] : (Nat.card H : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.card_pos (α := H)).ne'

/-- The intertwining dimension of two external tensors is the product of the local dimensions. -/
theorem finrank_intertwiningMap_externalRep [∀ i, Fintype (G i)]
    (V W : ∀ i, FDRep ℂ (G i)) :
    Module.finrank ℂ (IntertwiningMap (externalRep V).ρ (externalRep W).ρ) =
      ∏ i, Module.finrank ℂ (IntertwiningMap (V i).ρ (W i).ρ) := by
  classical
  let : ∀ i, Invertible (Nat.card (G i) : ℂ) := fun i =>
    invertibleOfNonzero (isUnit_card_complex (G i))
  let : Invertible (Nat.card (∀ i, G i) : ℂ) :=
    invertibleOfNonzero (isUnit_card_complex (∀ i, G i))
  apply Nat.cast_injective (R := ℂ)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank, Nat.cast_prod]
  simp_rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  change (Nat.card (∀ i, G i) : ℂ)⁻¹ *
    ∑ g : ∀ i, G i, (externalRep W).character g * (externalRep V).character g⁻¹ = _
  simp only [character_externalRep, ← Finset.prod_mul_distrib, Pi.inv_apply]
  rw [← Fintype.prod_sum (fun i (g : G i) => (W i).character g * (V i).character g⁻¹),
    Nat.card_pi, Nat.cast_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  rfl

/-- Reindexing the group along an isomorphism preserves the intertwining dimension. -/
theorem finrank_intertwiningMap_pullbackRep {H K : Type*} [Group H] [Group K]
    [Fintype H] [Fintype K] (f : H ≃* K) (V W : FDRep ℂ K) :
    Module.finrank ℂ (IntertwiningMap (pullbackRep f.toMonoidHom V).ρ
      (pullbackRep f.toMonoidHom W).ρ) = Module.finrank ℂ (IntertwiningMap V.ρ W.ρ) := by
  let : Invertible (Nat.card H : ℂ) := invertibleOfNonzero (isUnit_card_complex H)
  let : Invertible (Nat.card K : ℂ) := invertibleOfNonzero (isUnit_card_complex K)
  apply Nat.cast_injective (R := ℂ)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank,
    ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank, Nat.card_congr f.toEquiv]
  congr 1
  apply Fintype.sum_equiv f.toEquiv
  intro h
  change (pullbackRep f.toMonoidHom W).character h *
    (pullbackRep f.toMonoidHom V).character h⁻¹ = W.character (f h) * V.character (f h)⁻¹
  simp [map_inv]

section CharacterVectors

variable {H : Type*} [Group H]

/-- The vectors on which a representation transforms by a unit-valued character. -/
def characterVectors (V : FDRep ℂ H) (χ : H →* ℂˣ) : Submodule ℂ V where
  carrier := {v | ∀ g : H, V.ρ g v = (χ g : ℂ) • v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw g
    rw [map_add, smul_add, hv g, hw g]
  smul_mem' := by
    intro c v hv g
    rw [map_smul, hv g, smul_comm]

/-- Evaluation at `1` identifies intertwiners from a character with its vector eigenspace. -/
def oneDimensionalIntertwiningMapEquiv (V : FDRep ℂ H) (χ : H →* ℂˣ) :
    IntertwiningMap (oneDimensional χ).ρ V.ρ ≃ₗ[ℂ] characterVectors V χ := by
  let τ : Representation ℂ H ℂ := (oneDimensional χ).ρ
  change IntertwiningMap τ V.ρ ≃ₗ[ℂ] characterVectors V χ
  refine
    { toFun := fun f => ⟨f 1, fun g => ?_⟩
      invFun := fun v =>
        { toLinearMap := LinearMap.id.smulRight v.val
          isIntertwining' := fun g => ?_ }
      left_inv := fun f => ?_
      right_inv := fun v => Subtype.ext (one_smul ℂ v.val)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  · have h := IntertwiningMap.isIntertwining _ _ f g 1
    change f ((χ g : ℂ) • (1 : ℂ)) = V.ρ g (f 1) at h
    simpa only [map_smul] using h.symm
  · apply LinearMap.ext
    intro c
    change ((χ g : ℂ) * c) • v.val = V.ρ g (c • v.val)
    rw [map_smul, v.property g, smul_smul, mul_comm]
  · apply IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    change c • f 1 = f c
    rw [← map_smul]
    simp

end CharacterVectors

end Langlands.FiniteRep
