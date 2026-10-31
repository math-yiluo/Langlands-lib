import Langlands.Representation.Classification.UniformRefinementShuffleRealization
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Tensor.GLRefinement

/-! Actual uniform Levi conjugation in nested tensor coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification.ShuffleRefinement

open GeneralLinear Geometric CuspidalSupport

section Levi

variable {K : Type*} [Field K]
variable {m r : ℕ} (hr : 0 < r)
variable (B : BlockShape (m * r)) (w : Equiv.Perm (Fin (m * r)))
variable (S : BlockRefinement B)
variable (hS : sourceLevi K B (BlockShape.uniform m r hr) w = refinedLevi K B S)
variable (hw : IsMinimalRepresentative B (BlockShape.uniform m r hr) w)
variable (hdiv : ∀ j i, r ∣ (S j).size i)

include hw in
/-- Actual inverse permutation conjugation, expressed in nested Levi coordinates,
is the reindexing by the realized source-piece/target-block equivalence. -/
theorem flattenedLeviProductEquiv_leviConjugation_symm
    (z : (BlockShape.uniform m r hr).Levi K) :
    flattenedLeviProductEquiv K B S
        ((leviConjugation (B.flatten S) (BlockShape.uniform m r hr) w
          (conjugatesLevi_flatten_uniform hr B w S hS hdiv)).symm z) =
      (BlockShape.uniform m r hr).nestedLeviEquiv B S
        (refinementBlockEquiv hr B w S hS hdiv)
        (fun q => source_size_eq_of_dvd hr B w S hS q.1 q.2 (hdiv q.1 q.2)) K z := by
  let C := BlockShape.uniform m r hr
  let c := leviConjugation (B.flatten S) C w
    (conjugatesLevi_flatten_uniform hr B w S hS hdiv)
  funext j i
  apply Units.ext
  ext a b
  change flattenedLeviProductEquiv K B S (c.symm z) j i a b =
    z (refinementTargetIndex hr B w S j i)
      (Fin.cast (source_size_eq_of_dvd hr B w S hS j i (hdiv j i)) a)
      (Fin.cast (source_size_eq_of_dvd hr B w S hS j i (hdiv j i)) b)
  calc
    _ = B.leviEmbedding K (flattenedLeviEquiv K B S (c.symm z)).val
        (B.index j ((S j).index i a)) (B.index j ((S j).index i b)) := by
      change _ = B.leviEmbedding K
        (fun k => (S k).leviEmbedding K (flattenedLeviProductEquiv K B S (c.symm z) k))
        (B.index j ((S j).index i a)) (B.index j ((S j).index i b))
      rw [B.leviEmbedding_apply_same, (S j).leviEmbedding_apply_same]
    _ = C.leviEmbedding K z (w (B.index j ((S j).index i a)))
        (w (B.index j ((S j).index i b))) := by
      rw [flattenedLeviEquiv_embedding]
      change (B.flatten S).leviEmbedding K
        ((leviConjugation (B.flatten S) C w
          (conjugatesLevi_flatten_uniform hr B w S hS hdiv)).symm z) _ _ = _
      rw [leviConjugation_symm_embedding, mul_permutation_entry, permutation_inv,
        permutation_mul_entry, inv_inv]
    _ = _ := by
      rw [source_piece_coordinates hr B w S hS hw j i (hdiv j i) a,
        source_piece_coordinates hr B w S hS hw j i (hdiv j i) b,
        C.leviEmbedding_apply_same]

end Levi

section Tensor

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable {m r : ℕ} (hr : 0 < r)
variable (B : BlockShape (m * r)) (w : Equiv.Perm (Fin (m * r)))
variable (S : BlockRefinement B)
variable (hS : sourceLevi F.Carrier B (BlockShape.uniform m r hr) w =
  refinedLevi F.Carrier B S)
variable (hw : IsMinimalRepresentative B (BlockShape.uniform m r hr) w)
variable (hdiv : ∀ j i, r ∣ (S j).size i)

set_option maxHeartbeats 800000 in
include hw in
/-- The target tensor is equivalent to the nested tensor of its factors,
pulled from the flattened source by actual inverse Weyl conjugation. -/
def uniformRefinementTensorEquiv :
    letI := T.topology
    ∀ σ : ∀ t : Fin m, SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier),
      let τ := fun j i =>
        ((source_size_eq_of_dvd hr B w S hS j i (hdiv j i)).symm ▸
          σ (refinementTargetIndex hr B w S j i) :
            SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((S j).size i) F.Carrier))
      Representation.Equiv
        (FiniteTensor.external (fun t => (σ t).representation))
        (transport (B.flatten S) (BlockShape.uniform m r hr) w
          (conjugatesLevi_flatten_uniform hr B w S hS hdiv)
          ((FiniteTensor.external
            (fun j => FiniteTensor.external (fun i => (τ j i).representation))).comp
              (flattenedLeviProductEquiv F.Carrier B S).toMonoidHom)) := by
  letI := T.topology
  intro σ
  let C := BlockShape.uniform m r hr
  let e := refinementBlockEquiv hr B w S hS hdiv
  let hs := fun q : (j : Fin B.length) × Fin (S j).length =>
    source_size_eq_of_dvd hr B w S hS q.1 q.2 (hdiv q.1 q.2)
  let τ := fun j i => ((hs ⟨j, i⟩).symm ▸ σ (e ⟨j, i⟩) :
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear ((S j).size i) F.Carrier))
  let ρ := FiniteTensor.external
    (fun j => FiniteTensor.external (fun i => (τ j i).representation))
  let E := FiniteTensor.glRefinementEquiv F T C B S e hs σ
  refine Representation.Equiv.mk E.toLinearEquiv fun z => ?_
  have he := E.isIntertwining' (C.leviRefinementEquiv B S e hs F.Carrier z)
  change E.toLinearMap.comp
      ((FiniteTensor.external (fun t => (σ t).representation))
        ((C.leviRefinementEquiv B S e hs F.Carrier).symm
          (C.leviRefinementEquiv B S e hs F.Carrier z))) =
    (ρ ((refinedLeviEquiv F.Carrier B S).symm
      (C.leviRefinementEquiv B S e hs F.Carrier z))).comp E.toLinearMap at he
  rw [MulEquiv.symm_apply_apply] at he
  change E.toLinearMap.comp
      ((FiniteTensor.external (fun t => (σ t).representation)) z) =
    (ρ (flattenedLeviProductEquiv F.Carrier B S
      ((leviConjugation (B.flatten S) C w
        (conjugatesLevi_flatten_uniform hr B w S hS hdiv)).symm z))).comp E.toLinearMap
  rw [flattenedLeviProductEquiv_leviConjugation_symm hr B w S hS hw hdiv]
  simpa only [BlockShape.leviRefinementEquiv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] using he

end Tensor

end Langlands.Classification.ShuffleRefinement
