import Langlands.Representation.Aubert.CorrectedWholeTargetInterval
import Langlands.Representation.Aubert.WholeTargetSignedComparison

/-! Concrete whole-target interval data and lower concentration of actual grades. -/

noncomputable section

namespace Langlands.Aubert.ActualCutComplex

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
  (C : BlockShape n) (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
  (hwθ : w ∈ θ)
  (hbound : letI := T.topology
    CuspidalSupport.HasJacquetBlockBound F T C A)
  (hθ : ∀ v ∈ θ, ∀ z, Support.inversionLength v < Support.inversionLength z → z ∈ θ)
  (hLower : ∀ v ∈ θ \ {w}, ∀ z,
    Support.inversionLength v < Support.inversionLength z → z ∈ θ \ {w})

/-- Supply every field of the actual whole-target interval data, choosing its
common coefficient from the actual refinement at the smallest active cut set. -/
def concreteWholeTargetIntervalData
    (hinc : TypeASolomon.SourceIncreasing C w.symm)
    (hadj : WholeTarget.BlockEdgeAdjacent C w.symm) :
    Σ Q : BlockShape n, WholeTargetIntervalData T A C θ w
      (permutationDescents w) (WholeTarget.allowedCuts C w.symm) Q := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.fieldT2
  letI := T.generalLinearLocallyCompactSpace n
  let lower := permutationDescents w
  let upper := WholeTarget.allowedCuts C w.symm
  have hactive (s : Finset (Fin (n - 1)))
      (hs : CutComplex.BooleanInterval.Active lower upper s) :
      w ∈ Support.weylSupport (shape s) C θ ∧
        blockWeyl C ⊓ (blockWeyl (shape s)).comap
          (MulAut.conj w⁻¹).toMonoidHom = blockWeyl C := by
    apply (Support.weylSupport_wholeTarget_iff_active
      (shape s) C θ w hwθ hθ hLower hinc hadj).mpr
    simpa only [shape, BlockShape.cuts_cutEquiv_symm] using hs
  have hminimal (s : Finset (Fin (n - 1)))
      (hs : CutComplex.BooleanInterval.Active lower upper s) :
      IsMinimalRepresentative (shape s) C w :=
    (Support.mem_weylSupport_iff_minimal_of_upper_singleton
      (shape s) C θ w hwθ hθ hLower).mp (hactive s hs).1
  let S : ∀ s, CutComplex.BooleanInterval.Active lower upper s → BlockRefinement (shape s) :=
    fun s hs => Classical.choose
      (exists_standardIntersections F.Carrier (shape s) C w (hminimal s hs).1)
  have hS (s) (hs : CutComplex.BooleanInterval.Active lower upper s) :
      IsIntersectionRefinement (F := F.Carrier) (shape s) C w (S s hs) :=
    Classical.choose_spec
      (exists_standardIntersections F.Carrier (shape s) C w (hminimal s hs).1)
  have hlower : CutComplex.BooleanInterval.Active lower upper lower := by
    refine ⟨Finset.Subset.rfl, ?_⟩
    simpa only [lower, upper, Equiv.symm_symm] using
      WholeTarget.descents_subset_allowedCuts C w.symm hadj
  refine ⟨(shape lower).flatten (S lower hlower), {
    support := fun s hs => (hactive s hs).1
    increasing := fun s hs => (hminimal s hs).1
    refinement := S
    isIntersection := hS
    flatten_eq := ?_
    whole := fun s hs => (hactive s hs).2
    zero := ?_ }⟩
  · intro s hs
    exact wholeTarget_flattened_eq (F := F.Carrier) (shape s) (shape lower) C w
      (S s hs) (S lower hlower) (hS s hs).2.1 (hS lower hlower).2.1
      (hactive s hs).2 (hactive lower hlower).2
  · intro s hs
    have hnot : ¬ CutComplex.BooleanInterval.Active (permutationDescents w)
        (WholeTarget.allowedCuts C w.symm) (shape s).cuts := by
      simpa only [shape, BlockShape.cuts_cutEquiv_symm] using hs
    exact Support.cutSupportQuotient_subsingleton_of_not_active_interval.{uF,uV}
      T A (shape s) C θ w hbound hθ hLower hnot

/-- The concrete signed equivalence retains the actual common flattened
Jacquet coefficient at every active coordinate. -/
def concreteWholeTargetIntervalEquivalence
    (hinc : TypeASolomon.SourceIncreasing C w.symm)
    (hadj : WholeTarget.BlockEdgeAdjacent C w.symm) :
    Σ Q : BlockShape n, CutComplex.Diagram.Equivalence
      (bundledSupportQuotientDiagram T A C (θ \ {w}) θ)
      (WholeTarget.diagram C w.symm (Q.JacquetModule A.obj.ρ)) := by
  let data := concreteWholeTargetIntervalData T A C θ w hwθ hbound hθ hLower hinc hadj
  refine ⟨data.1, ?_⟩
  simpa only [WholeTarget.diagram, Equiv.symm_symm] using
    wholeTargetIntervalEquivalence T A C θ w (permutationDescents w)
      (WholeTarget.allowedCuts C w.symm) data.1 hθ hLower data.2

include hbound hθ hLower

/-- When either fixed inverse-permutation condition fails, every actual
homogeneous graded carrier is zero. -/
theorem bundledSupportQuotientDegree_subsingleton_of_not_fixed
    (hnot : ¬ (TypeASolomon.SourceIncreasing C w.symm ∧
      WholeTarget.BlockEdgeAdjacent C w.symm)) (k : ℕ) :
    Subsingleton ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).Degree k) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  constructor
  intro x y
  funext s
  have hfail : ¬ (TypeASolomon.SourceIncreasing C w.symm ∧
      WholeTarget.BlockEdgeAdjacent C w.symm ∧
      CutComplex.BooleanInterval.Active (permutationDescents w)
        (WholeTarget.allowedCuts C w.symm) (shape s.1).cuts) :=
    fun h => hnot ⟨h.1, h.2.1⟩
  exact (Support.cutSupportQuotient_subsingleton_of_not_wholeTarget_interval.{uF,uV}
    T A (shape s.1) C θ w hbound hθ hLower hfail).elim _ _

include hwθ

/-- The genuine signed graded differential is exact strictly below the
surviving target degree, with no remaining interval-data premise. -/
theorem bundledSupportQuotient_exact_below_target (k : ℕ)
    (hk : k + 1 < C.length - 1) :
    LinearMap.range
      ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential k) =
    LinearMap.ker
      ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential (k + 1)) := by
  by_cases hfixed : TypeASolomon.SourceIncreasing C w.symm ∧
      WholeTarget.BlockEdgeAdjacent C w.symm
  · let model := concreteWholeTargetIntervalEquivalence
      T A C θ w hwθ hbound hθ hLower hfixed.1 hfixed.2
    exact (model.2.degreeDifferential_exact_iff k).mpr
      (WholeTarget.exact_below_target C w.symm (model.1.JacquetModule A.obj.ρ)
        hfixed.2 k hk)
  · let := bundledSupportQuotientDegree_subsingleton_of_not_fixed
      T A C θ w hbound hθ hLower hfixed (k + 1)
    exact Subsingleton.elim _ _

/-- The initial genuine signed graded differential is injective whenever the
target degree is positive. -/
theorem bundledSupportQuotient_injective_before_target
    (hC : 0 < C.length - 1) :
    Function.Injective
      ((bundledSupportQuotientDiagram T A C (θ \ {w}) θ).degreeDifferential 0) := by
  by_cases hfixed : TypeASolomon.SourceIncreasing C w.symm ∧
      WholeTarget.BlockEdgeAdjacent C w.symm
  · let model := concreteWholeTargetIntervalEquivalence
      T A C θ w hwθ hbound hθ hLower hfixed.1 hfixed.2
    exact (model.2.degreeDifferential_injective_iff 0).mpr
      (WholeTarget.injective_before_target C w.symm (model.1.JacquetModule A.obj.ρ)
        hfixed.2 hC)
  · let := bundledSupportQuotientDegree_subsingleton_of_not_fixed
      T A C θ w hbound hθ hLower hfixed 0
    intro x y _
    exact Subsingleton.elim _ _

end Langlands.Aubert.ActualCutComplex
