import Langlands.Representation.CuspidalSupport.BlockPermutation
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.Tensor.FiniteRegrouping
import Langlands.Representation.Induction.BlockFactors

/-! Canonical block reordering and its actual action on external tensors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

variable {F : Type uF} [Field F] {n : ℕ} (B : BlockShape n)
  (e : Equiv.Perm (Fin B.length))

/-- The block labels determine both the target shape and a minimal actual
Levi-conjugating permutation. -/
theorem eq_blockPermutation_of_blockIndex {C : BlockShape n}
    (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F) B C w)
    (hmin : IsMinimalRepresentative B C w)
    (h : ∀ a, (blockIndex C (w a) : ℕ) = (e.symm (blockIndex B a) : ℕ)) :
    C = B.permute e ∧ w = B.blockPermutation e := by
  have heq := TotalConjugatingCount.eq_of_blockValue_eq (F := F) B
    ⟨C, ⟨⟨w, hmin⟩, hw⟩⟩
    ⟨B.permute e, ⟨⟨B.blockPermutation e,
      isMinimalRepresentative_blockPermutation B e⟩,
      conjugatesLevi_blockPermutation B e⟩⟩ (fun i => by
        change (blockIndex C (w (B.index i ⟨0, B.positive i⟩)) : ℕ) =
          (blockIndex (B.permute e)
            (B.blockPermutation e (B.index i ⟨0, B.positive i⟩)) : ℕ)
        rw [h, blockIndex_blockPermutation])
  exact ⟨congrArg Sigma.fst heq, congrArg (fun x => x.2.val.val) heq⟩

theorem leviConjugation_symm_blockPermutation
    (hw : ConjugatesLevi (F := F) B (B.permute e) (B.blockPermutation e)) :
    (leviConjugation B (B.permute e) (B.blockPermutation e) hw).symm =
      (FiniteTensor.reindexGroup (fun i => GeneralLinear (B.size i) F) e).symm := by
  apply MulEquiv.ext
  intro m
  funext k
  obtain ⟨i, rfl⟩ := e.surjective k
  rw [leviConjugation_symm_blockPermutation_apply]
  exact (FiniteTensor.reindexGroup_symm_apply_image
    (fun i => GeneralLinear (B.size i) F) e m i).symm

variable {V : Fin B.length → Type uV}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Actual Weyl transport of a block tensor is equivalent to the tensor
with its factors in the canonically permuted order. -/
def blockPermutationTensorEquiv
    (hw : ConjugatesLevi (F := F) B (B.permute e) (B.blockPermutation e))
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    Representation.Equiv
      (transport B (B.permute e) (B.blockPermutation e) hw (B.blockTensor ρ))
      ((B.permute e).blockTensor (fun i => ρ (e i))) :=
  Representation.Equiv.mk (FiniteTensor.reindexEquiv e ρ).toLinearEquiv
    (fun m => by
      change (FiniteTensor.reindexEquiv e ρ).toLinearMap ∘ₗ
        (B.blockTensor ρ) ((leviConjugation B (B.permute e)
          (B.blockPermutation e) hw).symm m) =
        ((B.permute e).blockTensor (fun i => ρ (e i))) m ∘ₗ
          (FiniteTensor.reindexEquiv e ρ).toLinearMap
      rw [leviConjugation_symm_blockPermutation]
      exact (FiniteTensor.reindexEquiv e ρ).isIntertwining' m)

@[simp] theorem blockPermutationTensorEquiv_tprod
    (hw : ConjugatesLevi (F := F) B (B.permute e) (B.blockPermutation e))
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (v : ∀ i, V i) :
    blockPermutationTensorEquiv B e hw ρ (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => v (e i)) :=
  FiniteTensor.reindexEquiv_tprod e ρ v

end Langlands.CuspidalSupport
