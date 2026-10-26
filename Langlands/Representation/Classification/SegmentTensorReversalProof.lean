import Langlands.Representation.Classification.SegmentTensorReversalStatement
import Langlands.Representation.Classification.Segments
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Tensor.FiniteRegrouping

/-! Association of the actual increasing and decreasing segment tensors. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData CuspidalSupport

universe uF uV

/-- Tensor reindexing intertwines the actual block permutation transport. -/
private def blockPermutationTensorEquiv
    {K : Type uF} [Field K] {n : ℕ} (B : BlockShape n)
    (e : Equiv.Perm (Fin B.length))
    {V : Fin B.length → Type uV} [hadd : ∀ i, AddCommGroup (V i)]
    [hmod : ∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) K) (V i)) :
    letI : ∀ i : Fin (B.permute e).length, AddCommGroup (V (e i)) :=
      fun i => hadd (e i)
    letI : ∀ i : Fin (B.permute e).length, Module ℂ (V (e i)) :=
      fun i => hmod (e i)
    (transport B (B.permute e) (B.blockPermutation e)
      (conjugatesLevi_blockPermutation B e) (FiniteTensor.external σ)).Equiv
      (FiniteTensor.external (fun i => σ (e i))) := by
  letI : ∀ i : Fin (B.permute e).length, AddCommGroup (V (e i)) :=
    fun i => hadd (e i)
  letI : ∀ i : Fin (B.permute e).length, Module ℂ (V (e i)) :=
    fun i => hmod (e i)
  let hw := conjugatesLevi_blockPermutation (F := K) B e
  have hL (g : (B.permute e).Levi K) :
      (leviConjugation B (B.permute e) (B.blockPermutation e) hw).symm g =
        (FiniteTensor.reindexGroup (fun i => GeneralLinear (B.size i) K) e).symm g := by
    apply (FiniteTensor.reindexGroup (fun i => GeneralLinear (B.size i) K) e).injective
    erw [MulEquiv.apply_symm_apply]
    funext i
    exact leviConjugation_symm_blockPermutation_apply B e hw g i
  refine Representation.Equiv.mk (FiniteTensor.reindexEquiv e σ).toLinearEquiv
    (fun g => ?_)
  apply LinearMap.ext
  intro x
  change FiniteTensor.reindexEquiv e σ
      (FiniteTensor.external σ
        ((leviConjugation B (B.permute e) (B.blockPermutation e) hw).symm g) x) = _
  rw [hL g]
  exact FiniteTensor.reindexEquiv_apply_action e σ g x

/-- Reversing the uniform blocks associates the actual two segment tensors.
This assertion concerns Levi tensors and requires no induction theorem. -/
theorem segmentFactors_associated_segmentFactorsDown
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    {r : ℕ} (m : ℕ) (hr : 0 < r)
    (A : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    RepresentationsAssociated (BlockShape.uniform m r hr) (BlockShape.uniform m r hr)
      (FiniteTensor.external (fun i => (T.segmentFactors A m hr i).representation))
      (FiniteTensor.external (fun i => (T.segmentFactorsDown A m hr i).representation)) := by
  let := T.topology
  let B := BlockShape.uniform m r hr
  let e : Equiv.Perm (Fin m) := Fin.revPerm
  let σ : Fin m → Representation ℂ (GeneralLinear r F.Carrier) A :=
    fun i => (T.segmentFactors A m hr i).representation
  let D : (FiniteTensor.external (fun i : Fin m => σ (e i))).Equiv
      (FiniteTensor.external
        (fun i : Fin m => (T.segmentFactorsDown A m hr i).representation)) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
    ext v
    change FiniteTensor.external (fun i => σ (e i)) g
        (PiTensorProduct.tprod ℂ v) =
      FiniteTensor.external
        (fun i => (T.segmentFactorsDown A m hr i).representation) g
        (PiTensorProduct.tprod ℂ v)
    erw [FiniteTensor.external_tprod, FiniteTensor.external_tprod]
    congr 1
    funext i
    change (T.segmentFactor A (i.rev.val : ℝ)).representation (g i) (v i) =
      (T.segmentFactor A ((m - 1 - i.val : ℕ) : ℝ)).representation (g i) (v i)
    have hi : i.rev.val = m - 1 - i.val := by
      rw [Fin.val_rev]
      omega
    rw [hi])
  exact ⟨B.blockPermutation e, conjugatesLevi_blockPermutation B e,
    ⟨(blockPermutationTensorEquiv B e σ).trans D⟩⟩

/-- Exact reversal association for the actual segment tensor families. -/
theorem segmentTensorReversalAssociation
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentTensorReversalAssociation.{uF,uV} F T := by
  let := T.topology
  intro r m hr A
  exact segmentFactors_associated_segmentFactorsDown F T m hr A

end Langlands.Classification
