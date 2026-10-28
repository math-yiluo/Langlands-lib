import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Representation.Parabolic.OrderedRefinementTensorInduction
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.CuspidalSupport.BlockPermutationTensor
import Mathlib.Data.Fin.Rev

/-! The actual inner tensors and both stages comparisons for an adjacent swap. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GeneralLinear.BlockShape

open Langlands.Geometric

variable {n : ℕ} (B : BlockShape n) (j : ℕ) (hj : j + 1 < B.length)

/-- Reversing each inner label performs precisely the global adjacent swap. -/
theorem adjacentBlockEquiv_rev (m : Fin (B.adjacentMerge j hj).length)
    (k : Fin (B.adjacentRefinement j hj m).length) :
    B.adjacentBlockEquiv j hj ⟨m, Fin.rev k⟩ =
      B.adjacentSwap j hj (B.adjacentBlockEquiv j hj ⟨m, k⟩) := by
  have hk := k.isLt
  change k.val < if m.val = j then 2 else 1 at hk
  have hv := B.adjacentBlockEquiv_val j hj ⟨m, k⟩
  have hvr := B.adjacentBlockEquiv_val j hj ⟨m, Fin.rev k⟩
  dsimp only at hv hvr
  change (B.adjacentBlockEquiv j hj ⟨m, Fin.rev k⟩).val =
    m.val + ((if m.val = j then 2 else 1) - (k.val + 1)) +
      (if j < m.val then 1 else 0) at hvr
  apply Fin.ext
  unfold adjacentSwap
  rw [Equiv.swap_apply_def]
  split_ifs with h₀ h₁
  · have hv₀ := congrArg Fin.val h₀
    dsimp only at hv₀ ⊢
    split_ifs at hk hvr hv <;> omega
  · have hv₁ := congrArg Fin.val h₁
    dsimp only at hv₁ ⊢
    split_ifs at hk hvr hv <;> omega
  · have hv₀ : (B.adjacentBlockEquiv j hj ⟨m,k⟩).val ≠ j := by
      intro h
      exact h₀ (Fin.ext h)
    have hv₁ : (B.adjacentBlockEquiv j hj ⟨m,k⟩).val ≠ j + 1 := by
      intro h
      exact h₁ (Fin.ext h)
    split_ifs at hk hvr hv <;> omega

/-- Reverse the order inside every inner block of the common merged shape. -/
def adjacentReverseRefinement : BlockRefinement (B.adjacentMerge j hj) :=
  fun m => (B.adjacentRefinement j hj m).permute Fin.revPerm

/-- The reversed inner sizes are exactly the sizes in the swapped global shape. -/
theorem adjacentReverse_size
    (a : (m : Fin (B.adjacentMerge j hj).length) ×
      Fin (B.adjacentReverseRefinement j hj m).length) :
    (B.adjacentReverseRefinement j hj a.1).size a.2 =
      (B.permute (B.adjacentSwap j hj)).size (B.adjacentBlockEquiv j hj a) :=
  congrArg B.size (B.adjacentBlockEquiv_rev j hj a.1 a.2)

/-- The reversed refinement uses the exact standard coordinates of the swapped shape. -/
theorem adjacentReverse_index (m : Fin (B.adjacentMerge j hj).length)
    (k : Fin (B.adjacentReverseRefinement j hj m).length)
    (x : Fin ((B.adjacentReverseRefinement j hj m).size k)) :
    (B.adjacentMerge j hj).index m ((B.adjacentReverseRefinement j hj m).index k x) =
      (B.permute (B.adjacentSwap j hj)).index (B.adjacentBlockEquiv j hj ⟨m,k⟩)
        (Fin.cast (B.adjacentReverse_size j hj ⟨m,k⟩) x) :=
  index_index_eq_of_lex (B.permute (B.adjacentSwap j hj)) (B.adjacentMerge j hj)
    (B.adjacentReverseRefinement j hj) (B.adjacentBlockEquiv j hj)
    (B.adjacentReverse_size j hj)
    (fun a b hab => (B.adjacentBlockEquiv_lt_iff j hj a b).mpr hab) m k x

end Langlands.GeneralLinear.BlockShape

namespace Langlands.CuspidalSupport

open GeneralLinear Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (j : ℕ) (hj : j + 1 < B.length)

/-- The actual supercuspidal tensor inside each original merged block. -/
def adjacentInnerTensor :
    letI := T.topology
    (∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) →
      RefinedInductionTensor.Factors.{uF,uV} F T (B.adjacentMerge j hj)
        (B.adjacentRefinement j hj) :=
  letI := T.topology
  fun A m => FiniteTensor.externalSmoothObject
    (fun k => (A (B.adjacentBlockEquiv j hj ⟨m,k⟩)).obj)

/-- The actual supercuspidal tensor with each inner order reversed. -/
def adjacentReverseTensor :
    letI := T.topology
    (∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) →
      RefinedInductionTensor.Factors.{uF,uV} F T (B.adjacentMerge j hj)
        (B.adjacentReverseRefinement j hj) :=
  letI := T.topology
  fun A m => FiniteTensor.externalSmoothObject
    (fun k => (A (B.adjacentBlockEquiv j hj ⟨m,Fin.rev k⟩)).obj)

private theorem family_rankCast_eq {ι : Sort*} (r : ι → ℕ) {X : ℕ → Sort*}
    (A : ∀ i, X (r i)) {a b : ι} (hab : a = b) (h : r a = r b) :
    (h.symm ▸ A b : X (r a)) = A a := by
  subst b
  rfl

/-- The regrouped target factors are the actual reversed inner tensor objects,
including the transports of their carriers. -/
theorem adjacentReverseTensorFactors_eq :
    letI := T.topology
    ∀ A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i),
      orderedRefinementTensorFactors F T (B.permute (B.adjacentSwap j hj))
        (B.adjacentMerge j hj) (B.adjacentReverseRefinement j hj)
        (B.adjacentBlockEquiv j hj) (B.adjacentReverse_size j hj)
        (fun i => (A (B.adjacentSwap j hj i)).obj) =
      adjacentReverseTensor F T B j hj A := by
  let := T.topology
  intro A
  funext m
  apply congrArg FiniteTensor.externalSmoothObject
  funext k
  exact family_rankCast_eq B.size
    (X := fun r => SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    (fun i => (A i).obj)
    (B.adjacentBlockEquiv_rev j hj m k) (B.adjacentReverse_size j hj ⟨m,k⟩)

/-- The actual outer action induced from the normalized original inner tensors. -/
def adjacentTensorOuterInduced
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  T.normalizedParabolicInduced (B.adjacentMerge j hj)
    (RefinedInductionTensor.externalRepresentation F T (B.adjacentMerge j hj)
      (B.adjacentRefinement j hj) (adjacentInnerTensor F T B j hj A))

/-- The actual outer action induced from the normalized reversed inner tensors. -/
def adjacentReverseTensorOuterInduced
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  T.normalizedParabolicInduced (B.adjacentMerge j hj)
    (RefinedInductionTensor.externalRepresentation F T (B.adjacentMerge j hj)
      (B.adjacentReverseRefinement j hj) (adjacentReverseTensor F T B j hj A))

/-- The source normalized product is outer induction of the actual normalized
inner tensor inductions in the common merged shape. -/
def adjacentTensorStagesEquiv
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  orderedRefinementTensorInductionEquiv F T B (B.adjacentMerge j hj)
    (B.adjacentRefinement j hj) (B.adjacentBlockEquiv j hj)
    (B.adjacentBlock_size j hj) (B.adjacent_index j hj) (fun i => (A i).obj)

private def stagesFactorsCast {r : ℕ} (D : BlockShape r)
    (S : Langlands.Geometric.BlockRefinement D)
    {A A' : RefinedInductionTensor.Factors.{uF,uV} F T D S} (h : A = A')
    {V : Type*} {_ : AddCommMonoid V} {_ : Module ℂ V}
    {ρ : Representation ℂ (GeneralLinear r F.Carrier) V}
    (E : Representation.Equiv ρ
      (T.normalizedParabolicInduced D
        (RefinedInductionTensor.externalRepresentation F T D S A))) :
    Representation.Equiv ρ
      (T.normalizedParabolicInduced D
        (RefinedInductionTensor.externalRepresentation F T D S A')) := by
  subst A'
  exact E

/-- The swapped normalized product is outer induction of the actual reversed
inner tensor inductions in the same merged shape. -/
def adjacentReverseTensorStagesEquiv
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  stagesFactorsCast F T (B.adjacentMerge j hj) (B.adjacentReverseRefinement j hj)
    (adjacentReverseTensorFactors_eq F T B j hj A)
    (orderedRefinementTensorInductionEquiv F T
      (B.permute (B.adjacentSwap j hj)) (B.adjacentMerge j hj)
      (B.adjacentReverseRefinement j hj) (B.adjacentBlockEquiv j hj)
      (B.adjacentReverse_size j hj) (B.adjacentReverse_index j hj)
      (fun i => (A (B.adjacentSwap j hj i)).obj))

/-- Both actual inner tensors are irreducible and Levi-cuspidal. -/
theorem adjacentInnerTensors_cuspidal :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i))
      (m : Fin (B.adjacentMerge j hj).length),
      ((adjacentInnerTensor F T B j hj A m).IsIrreducible ∧
        IsLeviCuspidal (B.adjacentRefinement j hj m)
          (adjacentInnerTensor F T B j hj A m).representation) ∧
      ((adjacentReverseTensor F T B j hj A m).IsIrreducible ∧
        IsLeviCuspidal (B.adjacentReverseRefinement j hj m)
          (adjacentReverseTensor F T B j hj A m).representation) := by
  let := T.topology
  intro A m
  exact ⟨glCuspidalTensor p F T _ ((B.adjacentMerge j hj).positive m)
      (B.adjacentRefinement j hj m) (fun k => A (B.adjacentBlockEquiv j hj ⟨m,k⟩)),
    glCuspidalTensor p F T _ ((B.adjacentMerge j hj).positive m)
      (B.adjacentReverseRefinement j hj m)
      (fun k => A (B.adjacentBlockEquiv j hj ⟨m,Fin.rev k⟩))⟩

/-- The canonical inner block permutation carries each source tensor to its
actual reversed tensor. -/
def adjacentInnerTensorTransportEquiv :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i))
      (m : Fin (B.adjacentMerge j hj).length),
      Representation.Equiv
        (transport (B.adjacentRefinement j hj m) (B.adjacentReverseRefinement j hj m)
          ((B.adjacentRefinement j hj m).blockPermutation Fin.revPerm)
          (conjugatesLevi_blockPermutation (F := F.Carrier)
            (B.adjacentRefinement j hj m) Fin.revPerm)
          (adjacentInnerTensor F T B j hj A m).representation)
        (adjacentReverseTensor F T B j hj A m).representation := by
  letI := T.topology
  intro A m
  exact blockPermutationTensorEquiv (B.adjacentRefinement j hj m) Fin.revPerm
    (conjugatesLevi_blockPermutation (F := F.Carrier)
      (B.adjacentRefinement j hj m) Fin.revPerm)
    (fun k => (A (B.adjacentBlockEquiv j hj ⟨m,k⟩)).obj.representation)

end Langlands.CuspidalSupport
