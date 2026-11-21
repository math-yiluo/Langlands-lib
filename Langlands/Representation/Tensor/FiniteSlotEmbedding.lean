import Langlands.Representation.Tensor.ExternalSubquotient
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.TensorProduct.MultiplicityCancellation

/-! # Equivariant embeddings of factors into a finite tensor -/

noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace Langlands.FiniteTensor

variable {ι : Type*} [DecidableEq ι] {V : ι → Type*}
  [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

/-- Insert a vector into one slot while fixing a tensor of the other slots. -/
def slotEmbedding (i : ι) (y : ⨂[ℂ] j : ({i}ᶜ : Set ι), V j) :
    V i →ₗ[ℂ] (⨂[ℂ] j, V j) :=
  (PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V i).symm.toLinearMap ∘ₗ
    TensorProduct.mk ℂ _ _ y

/-- The insertion is injective for a nonzero complementary tensor. -/
theorem slotEmbedding_injective (i : ι) (y : ⨂[ℂ] j : ({i}ᶜ : Set ι), V j)
    (hy : y ≠ 0) : Function.Injective (slotEmbedding i y) := by
  let E := PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V i
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  by_contra hxne
  apply TensorMultiplicity.tmul_ne_zero (K := ℂ) hy hxne
  change E.symm (y ⊗ₜ[ℂ] x) = 0 at hx
  exact E.symm.injective (hx.trans (E.symm.map_zero).symm)

/-- Insertion intertwines any endomorphism of the factor with its one-slot action. -/
theorem map_slotEmbedding (i : ι) (y : ⨂[ℂ] j : ({i}ᶜ : Set ι), V j)
    (T : Module.End ℂ (V i)) (x : V i) :
    PiTensorProduct.map (slot i T) (slotEmbedding i y x) = slotEmbedding i y (T x) := by
  let E := PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V i
  apply E.injective
  rw [split_map_slot]
  simp [E, slotEmbedding]

/-- Nontrivial factors in the other slots give a simultaneous embedding for all
one-slot operators. -/
theorem exists_slotEmbedding [Finite ι] (i : ι)
    (hne : ∀ j, j ≠ i → Nontrivial (V j)) :
    ∃ f : V i →ₗ[ℂ] (⨂[ℂ] j, V j), Function.Injective f ∧
      ∀ (T : Module.End ℂ (V i)) x, PiTensorProduct.map (slot i T) (f x) = f (T x) := by
  have : Nontrivial (⨂[ℂ] j : ({i}ᶜ : Set ι), V j) :=
    nontrivial_piTensorProduct fun j => hne j j.property
  obtain ⟨y, hy⟩ := exists_ne (0 : ⨂[ℂ] j : ({i}ᶜ : Set ι), V j)
  exact ⟨slotEmbedding i y, slotEmbedding_injective i y hy, map_slotEmbedding i y⟩

end Langlands.FiniteTensor
