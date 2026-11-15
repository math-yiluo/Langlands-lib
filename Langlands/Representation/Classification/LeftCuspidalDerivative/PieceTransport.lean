import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Tensor.ProductFiltration

/-!
# Weyl transport of block tensors along minimal representatives

* A minimal representative for two block shapes is still minimal for their flattened
  refinements.
* The inverse whole-Levi conjugation along a minimal representative is, block by block, the
  rank reindexing of the corresponding target block.
* Consequently the Weyl transport of a block tensor is the block tensor of the relabelled
  factors, each transported along the literal rank equality.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear Geometric CuspidalSupport

universe uF uV

section Minimal

variable {n : ℕ} {B C : BlockShape n} {w : Equiv.Perm (Fin n)}

/-- Minimality survives flattening of refinements of both shapes: every flattened block is a
consecutive part of a block of the original shape. -/
theorem isMinimalRepresentative_flatten (S : BlockRefinement B) (R : BlockRefinement C)
    (hmin : IsMinimalRepresentative B C w) :
    IsMinimalRepresentative (B.flatten S) (C.flatten R) w := by
  constructor
  · intro k a b hab
    change w ((B.flatten S).index k a) < w ((B.flatten S).index k b)
    rw [B.flatten_index S k a, B.flatten_index S k b]
    exact hmin.1 _ (index_strictMono _ _ hab)
  · intro k a b hab
    change w.symm ((C.flatten R).index k a) < w.symm ((C.flatten R).index k b)
    rw [C.flatten_index R k a, C.flatten_index R k b]
    exact hmin.2 _ (index_strictMono _ _ hab)

end Minimal

section Entries

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n} {w : Equiv.Perm (Fin n)}

/-- The block sizes matched by the block bijection of a conjugating permutation. -/
theorem size_blockEquiv_symm (hw : ConjugatesLevi (F := F) B C w) (j : Fin C.length) :
    B.size ((blockEquiv hw).symm j) = C.size j := by
  have h := size_blockMap hw ((blockEquiv hw).symm j)
  have hj : blockMap B C w ((blockEquiv hw).symm j) = j := (blockEquiv hw).apply_symm_apply j
  rw [hj] at h
  exact h

/-- Entry formula for inverse whole-Levi conjugation with a free target block. -/
theorem leviConjugation_symm_entry_of_eq (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) B C w) (m : C.Levi F) (i : Fin B.length)
    (j : Fin C.length) (hij : blockMap B C w i = j) (h : B.size i = C.size j)
    (a b : Fin (B.size i)) :
    (leviConjugation B C w hw).symm m i a b = m j (Fin.cast h a) (Fin.cast h b) := by
  subst hij
  exact leviConjugation_symm_block_entry hmin hw m i a b

/-- Block by block, inverse whole-Levi conjugation along a minimal representative is the
rank reindexing of the corresponding target block. -/
theorem leviConjugation_symm_apply_blockEquiv_symm (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) B C w) (m : C.Levi F) (j : Fin C.length) :
    (leviConjugation B C w hw).symm m ((blockEquiv hw).symm j) =
      (GeneralLinear.reindex (R := F) (finCongr (size_blockEquiv_symm hw j))).symm (m j) := by
  apply Units.ext
  funext a b
  rw [leviConjugation_symm_entry_of_eq hmin hw m _ j ((blockEquiv hw).apply_symm_apply j)
    (size_blockEquiv_symm hw j) a b]
  rfl

end Entries

section Tensor

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n} {w : Equiv.Perm (Fin n)}
  {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The Weyl transport of a block tensor along a minimal representative is the block tensor
of the relabelled factors, each pulled back along the rank reindexing. -/
def transportBlockTensorEquiv (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F) B C w)
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    (transport B C w hw (B.blockTensor ρ)).Equiv
      (FiniteTensor.external (fun j : Fin C.length =>
        (ρ ((blockEquiv hw).symm j)).comp
          (GeneralLinear.reindex (R := F)
            (finCongr (size_blockEquiv_symm hw j))).symm.toMonoidHom)) :=
  Representation.Equiv.mk (PiTensorProduct.reindex ℂ V (blockEquiv hw)) (fun m => by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      transport, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, FiniteTensor.external_tprod,
      PiTensorProduct.reindex_tprod]
    congr 1
    funext j
    rw [leviConjugation_symm_apply_blockEquiv_symm hmin hw m j])

end Tensor

section Smooth

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} {B C : BlockShape n} {w : Equiv.Perm (Fin n)}

/-- The Weyl transport of an external tensor of smooth factors along a minimal
representative is the external tensor of the relabelled factors, rank-cast to the target
blocks. -/
def transportExternalCastEquiv (hmin : IsMinimalRepresentative B C w)
    (hw : ConjugatesLevi (F := F.Carrier) B C w)
    (X : letI := T.topology
      ∀ k : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size k) F.Carrier)) :
    letI := T.topology
    (transport B C w hw (FiniteTensor.external (fun k => (X k).representation))).Equiv
      (FiniteTensor.external (fun j : Fin C.length =>
        (T.castRank (size_blockEquiv_symm hw j) (X ((blockEquiv hw).symm j))).representation)) :=
  letI := T.topology
  (transportBlockTensorEquiv hmin hw (fun k => (X k).representation)).trans
    (FiniteTensorFiltration.externalCongr (fun j =>
      T.castRankEquiv (size_blockEquiv_symm hw j) (X ((blockEquiv hw).symm j))))

end Smooth

end Langlands.Classification.LeftCuspidalDerivative
