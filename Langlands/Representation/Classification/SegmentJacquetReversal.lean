import Langlands.Representation.Classification.Segments
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
import Langlands.Representation.Filtration.MultiplicityTransportProof

/-!
# Reversing the test tensor in segment Jacquet multiplicities

The actual block reversal compares upper and opposite Jacquet multiplicities
for every ambient representation, without an induction or constituent premise.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData
open CuspidalJacquetMultiplicity OppositeCuspidalJacquetFiltration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {r : ℕ}

/-- Pulling the increasing tensor back along block reversal gives the
decreasing tensor by actual tensor reindexing. -/
def segmentTensorReverseEquiv (m : ℕ) (hr : 0 < r)
    (A : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    let B := BlockShape.uniform m r hr
    Representation.Equiv
      ((FiniteTensor.external
        (fun i => (T.segmentFactors A m hr i).representation)).comp
          (leviReverseEquiv B).toMonoidHom)
      (FiniteTensor.external
        (fun i => (T.segmentFactorsDown A m hr i).representation)) := by
  letI := T.topology
  let B := BlockShape.uniform m r hr
  let σ : Fin m → Representation ℂ (GeneralLinear r F.Carrier) A :=
    fun i => (T.segmentFactors A m hr i).representation
  let e := FiniteTensor.reindexEquiv Fin.revPerm σ
  have hrev (g : B.Levi F.Carrier) :
      leviReverseEquiv B g =
        (FiniteTensor.reindexGroup
          (fun _ : Fin m => GeneralLinear r F.Carrier) Fin.revPerm).symm g := by
    funext i
    change g i.rev = _
    have hi := (FiniteTensor.reindexGroup_symm_apply_image
      (fun _ : Fin m => GeneralLinear r F.Carrier) Fin.revPerm g i.rev).symm
    change g i.rev =
      (FiniteTensor.reindexGroup
        (fun _ : Fin m => GeneralLinear r F.Carrier) Fin.revPerm).symm g i.rev.rev at hi
    simpa only [Fin.rev_rev] using hi
  let E : Representation.Equiv
      ((FiniteTensor.external σ).comp (leviReverseEquiv B).toMonoidHom)
      (FiniteTensor.external (fun i => σ i.rev)) :=
    Representation.Equiv.mk e.toLinearEquiv (fun g => by
      change e.toLinearEquiv.toLinearMap.comp
          ((FiniteTensor.external σ) (leviReverseEquiv B g)) =
        (FiniteTensor.external (fun i => σ i.rev) g).comp e.toLinearEquiv.toLinearMap
      rw [hrev]
      exact e.isIntertwining' g)
  refine E.trans ?_
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => ?_)
  ext v
  change FiniteTensor.external (fun i => σ i.rev) g (PiTensorProduct.tprod ℂ v) =
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
    change m - (i.val + 1) = m - 1 - i.val
    omega
  rw [hi]

/-- Actual tensor reindexing reverses the decreasing tensor back to the
increasing tensor. -/
def segmentTensorDownReverseEquiv (m : ℕ) (hr : 0 < r)
    (A : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    let B := BlockShape.uniform m r hr
    Representation.Equiv
      ((FiniteTensor.external
        (fun i => (T.segmentFactorsDown A m hr i).representation)).comp
          (leviReverseEquiv B).toMonoidHom)
      (FiniteTensor.external
        (fun i => (T.segmentFactors A m hr i).representation)) := by
  letI := T.topology
  let B := BlockShape.uniform m r hr
  let τ : Fin m → Representation ℂ (GeneralLinear r F.Carrier) A :=
    fun i => (T.segmentFactorsDown A m hr i).representation
  let e := FiniteTensor.reindexEquiv Fin.revPerm τ
  have hrev (g : B.Levi F.Carrier) :
      leviReverseEquiv B g =
        (FiniteTensor.reindexGroup
          (fun _ : Fin m => GeneralLinear r F.Carrier) Fin.revPerm).symm g := by
    funext i
    change g i.rev = _
    have hi := (FiniteTensor.reindexGroup_symm_apply_image
      (fun _ : Fin m => GeneralLinear r F.Carrier) Fin.revPerm g i.rev).symm
    change g i.rev =
      (FiniteTensor.reindexGroup
        (fun _ : Fin m => GeneralLinear r F.Carrier) Fin.revPerm).symm g i.rev.rev at hi
    simpa only [Fin.rev_rev] using hi
  let E : Representation.Equiv
      ((FiniteTensor.external τ).comp (leviReverseEquiv B).toMonoidHom)
      (FiniteTensor.external (fun i => τ i.rev)) :=
    Representation.Equiv.mk e.toLinearEquiv (fun g => by
      change e.toLinearEquiv.toLinearMap.comp
          ((FiniteTensor.external τ) (leviReverseEquiv B g)) =
        (FiniteTensor.external (fun i => τ i.rev) g).comp e.toLinearEquiv.toLinearMap
      rw [hrev]
      exact e.isIntertwining' g)
  refine E.trans ?_
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => ?_)
  ext v
  change FiniteTensor.external (fun i => τ i.rev) g (PiTensorProduct.tprod ℂ v) =
    FiniteTensor.external
      (fun i => (T.segmentFactors A m hr i).representation) g
      (PiTensorProduct.tprod ℂ v)
  erw [FiniteTensor.external_tprod, FiniteTensor.external_tprod]
  congr 1
  funext i
  change (T.segmentFactor A ((m - 1 - i.rev.val : ℕ) : ℝ)).representation (g i) (v i) =
    (T.segmentFactor A (i.val : ℝ)).representation (g i) (v i)
  have hi : m - 1 - i.rev.val = i.val := by
    have him : i.val < m := i.isLt
    rw [Fin.val_rev]
    change m - 1 - (m - (i.val + 1)) = i.val
    omega
  rw [hi]

/-- For an arbitrary actual ambient representation, the increasing test
tensor's upper Jacquet count is the decreasing test tensor's opposite count. -/
theorem segment_upper_opposite_multiplicity_iff (m : ℕ) (hr : 0 < r)
    (A : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    (P : Rep.{uW} ℂ (GeneralLinear (m * r) F.Carrier)) (k : ℕ) :
    letI := T.topology
    let B := BlockShape.uniform m r hr
    let σ := Rep.of (FiniteTensor.external
      (fun i => (T.segmentFactors A m hr i).representation))
    let τ := Rep.of (FiniteTensor.external
      (fun i => (T.segmentFactorsDown A m hr i).representation))
    HasJordanHolderMultiplicity (upperJacquet T B P) σ k ↔
      HasJordanHolderMultiplicity (oppositeJacquet T B P) τ k := by
  let := T.topology
  let B := BlockShape.uniform m r hr
  let σ := Rep.of (FiniteTensor.external
    (fun i => (T.segmentFactors A m hr i).representation))
  let τ := Rep.of (FiniteTensor.external
    (fun i => (T.segmentFactorsDown A m hr i).representation))
  have h := groupEquivJordanHolderMultiplicityTransport ℂ
    (B.reverse.Levi F.Carrier) (B.Levi F.Carrier)
    (leviReverseEquiv B) (upperJacquet T B.reverse P) σ k
  have htransport := equivJordanHolderMultiplicityTransport ℂ (B.Levi F.Carrier)
    (Rep.of ((T.normalizedJacquet B.reverse P.ρ).comp (leviReverseEquiv B).toMonoidHom))
    (oppositeJacquet T B P)
    (Rep.of (σ.ρ.comp (leviReverseEquiv B).toMonoidHom)) τ
    (oppositeJacquetReverseEquiv T B P) (segmentTensorReverseEquiv T m hr A) k
  exact h.trans htransport

/-- The opposite count for the increasing test equals the upper count for
the decreasing test, with the same unrestricted ambient representation. -/
theorem segment_opposite_upper_multiplicity_iff (m : ℕ) (hr : 0 < r)
    (A : letI := T.topology;
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    (P : Rep.{uW} ℂ (GeneralLinear (m * r) F.Carrier)) (k : ℕ) :
    letI := T.topology
    let B := BlockShape.uniform m r hr
    let σ := Rep.of (FiniteTensor.external
      (fun i => (T.segmentFactors A m hr i).representation))
    let τ := Rep.of (FiniteTensor.external
      (fun i => (T.segmentFactorsDown A m hr i).representation))
    HasJordanHolderMultiplicity (oppositeJacquet T B P) σ k ↔
      HasJordanHolderMultiplicity (upperJacquet T B P) τ k := by
  let := T.topology
  let B := BlockShape.uniform m r hr
  let σ := Rep.of (FiniteTensor.external
    (fun i => (T.segmentFactors A m hr i).representation))
  let τ := Rep.of (FiniteTensor.external
    (fun i => (T.segmentFactorsDown A m hr i).representation))
  have h := groupEquivJordanHolderMultiplicityTransport ℂ
    (B.reverse.Levi F.Carrier) (B.Levi F.Carrier)
    (leviReverseEquiv B) (upperJacquet T B.reverse P) τ k
  have htransport := equivJordanHolderMultiplicityTransport ℂ (B.Levi F.Carrier)
    (Rep.of ((T.normalizedJacquet B.reverse P.ρ).comp (leviReverseEquiv B).toMonoidHom))
    (oppositeJacquet T B P)
    (Rep.of (τ.ρ.comp (leviReverseEquiv B).toMonoidHom)) σ
    (oppositeJacquetReverseEquiv T B P) (segmentTensorDownReverseEquiv T m hr A) k
  exact (h.trans htransport).symm

end Langlands.Classification
