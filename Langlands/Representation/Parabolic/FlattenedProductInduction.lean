import Langlands.Representation.Parabolic.OrderedRefinementTensorInduction
import Langlands.Representation.Parabolic.FlattenedTensorOccurrences

/-! Actual product induction for a supplied nested family in consecutive order. -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- List a supplied nested family in the standard consecutive flattened order. -/
def flattenedSmoothFamily :
    letI := T.topology
    (∀ i j, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((S i).size j) F.Carrier)) →
    ∀ k, SmoothRep.{0, uF, uV} ℂ
      (GeneralLinear ((B.flatten S).size k) F.Carrier) :=
  letI := T.topology
  fun C k => C ((B.flattenBlockEquiv S).symm k).1
    ((B.flattenBlockEquiv S).symm k).2

/-- Inducing the consecutive flattened family agrees with the actual outer
product of the actual inner inductions, with all rank transports included. -/
def flattenedProductInducedEquiv :
    letI := T.topology
    ∀ C : ∀ i j, SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((S i).size j) F.Carrier),
      Representation.Equiv
        (T.normalizedProductInduced (B.flatten S)
          (fun k => (flattenedSmoothFamily F T B S C k).representation))
        (T.normalizedProductInduced B (fun i =>
          T.normalizedProductInduced (S i) (fun j => (C i j).representation))) := by
  let := T.topology
  intro C
  let e := B.flattenBlockEquiv S
  let hs := fun q => (B.flatten_size_flattenBlockEquiv S q).symm
  have hc : ∀ i j (x : Fin ((S i).size j)),
      B.index i ((S i).index j x) =
        (B.flatten S).index (e ⟨i, j⟩) (Fin.cast (hs ⟨i, j⟩) x) :=
    fun i j x => B.index_index_eq_flatten S ⟨i, j⟩ x
  have hcast {r s : ℕ} (h : r = s)
      (Y : SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
      HEq (h ▸ Y : SmoothRep.{0, uF, uV} ℂ (GeneralLinear s F.Carrier)) Y := by
    cases h
    rfl
  have hdep (q q' : Σ i, Fin (S i).length) (h : q = q') :
      HEq (C q.1 q.2) (C q'.1 q'.2) := by
    cases h
    rfl
  have hA : orderedRefinementTensorFactors F T (B.flatten S) B S e hs
      (flattenedSmoothFamily F T B S C) =
        (fun i => FiniteTensor.externalSmoothObject (C i)) := by
    funext i
    apply congrArg FiniteTensor.externalSmoothObject
    funext j
    exact eq_of_heq ((hcast (hs ⟨i, j⟩).symm _).trans
      (hdep _ _ (e.symm_apply_apply ⟨i, j⟩)))
  change Representation.Equiv
    (T.normalizedProductInduced (B.flatten S)
      (fun k => (flattenedSmoothFamily F T B S C k).representation))
    (T.normalizedParabolicInduced B
      (RefinedInductionTensor.externalRepresentation F T B S
        (fun i => FiniteTensor.externalSmoothObject (C i))))
  exact Eq.ndrec
    (motive := fun Z : RefinedInductionTensor.Factors.{uF, uV} F T B S =>
      Representation.Equiv
        (T.normalizedProductInduced (B.flatten S)
          (fun k => (flattenedSmoothFamily F T B S C k).representation))
        (T.normalizedParabolicInduced B
          (RefinedInductionTensor.externalRepresentation F T B S Z)))
    (orderedRefinementTensorInductionEquiv.{uF, uV}
      F T (B.flatten S) B S e hs hc (flattenedSmoothFamily F T B S C))
    hA

end Langlands.Parabolic
