import Langlands.Sheaf.Renard.ProjectorPresheaf

/-!
# Intrinsic gluing for the original-action projector presheaf
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Langlands.Algebra Langlands.HarmonicAnalysis

universe u v w

namespace Langlands.Sheaf.Renard.ProjectorBasisSheaf

variable {X : Type u} [TopologicalSpace X]
  (hX : Langlands.Topology.IsLocallyProfinite X)
  (M : Type v) [AddCommGroup M] [NonUnitalModule (PointwiseTestAlgebra.Carrier X) M]

/-- A section on a smaller compact open is fixed by every larger compact open. -/
theorem value_fixed_of_le {U V : CompactOpen hX} (h : U.obj ≤ V.obj)
    (s : Value hX M U) : action hX M V s.val = s.val :=
  Idempotent.smul_eq_of_le
    (PointwiseTestAlgebra.characteristicIdempotent_le _ _ _ _ h) s.property

/-- Literal overlap compatibility gives the cross-projection equality. -/
theorem compatible_action {ι : Type w} {U : ι → CompactOpen hX}
    {s : ∀ i, Value hX M (U i)}
    (hs : Compatible (rawPresheaf hX M) U s) (i j : ι) :
    action hX M (U i) (s j).val = action hX M (U j) (s i).val := by
  have he := congrArg Subtype.val
    (hs i j (interOpen hX (U i) (U j)) inf_le_left inf_le_right)
  change action hX M (interOpen hX (U i) (U j)) (s i).val =
    action hX M (interOpen hX (U i) (U j)) (s j).val at he
  calc
    action hX M (U i) (s j).val =
        action hX M (interOpen hX (U i) (U j)) (s j).val := by
      rw [← action_mul, value_fixed]
    _ = action hX M (interOpen hX (U i) (U j)) (s i).val := he.symm
    _ = action hX M (U j) (s i).val := by
      rw [← action_mul, action_comm, value_fixed]

/-- The original test which is the characteristic of a finite union. -/
def finiteTest {ι : Type w} (t : Finset ι) (U : ι → CompactOpen hX) :
    PointwiseTestAlgebra.Carrier X :=
  PointwiseTestAlgebra.finiteUnionCharacteristic t (fun i => (U i).obj)
    (fun i => clopen hX (U i)) (fun i => compact hX (U i))

/-- Its action is still the specified original action. -/
def finiteAction {ι : Type w} (t : Finset ι) (U : ι → CompactOpen hX) : M →+ M :=
  NonUnitalModuleCorner.originalAction (finiteTest hX t U)

@[simp] theorem finiteAction_empty {ι : Type w} (U : ι → CompactOpen hX) (m : M) :
    finiteAction hX M ∅ U m = 0 := by
  change NonUnitalModuleCorner.originalAction
    (PointwiseTestAlgebra.finiteUnionCharacteristic ∅ _ _ _) m = 0
  rw [PointwiseTestAlgebra.finiteUnionCharacteristic_empty,
    NonUnitalModuleCorner.originalAction_zero]

theorem finiteAction_insert {ι : Type w} [DecidableEq ι]
    (t : Finset ι) (i : ι) (U : ι → CompactOpen hX) (m : M) :
    finiteAction hX M (insert i t) U m =
      action hX M (U i) m + finiteAction hX M t U m -
        action hX M (U i) (finiteAction hX M t U m) := by
  change NonUnitalModuleCorner.originalAction
    (PointwiseTestAlgebra.finiteUnionCharacteristic (insert i t) _ _ _) m = _
  rw [PointwiseTestAlgebra.finiteUnionCharacteristic_insert]
  simp only [map_sub, map_add]
  change action hX M (U i) m + finiteAction hX M t U m -
    NonUnitalModuleCorner.originalAction (test hX (U i) * finiteTest hX t U) m = _
  rw [NonUnitalModuleCorner.originalAction_mul]
  rfl

/-- Agreement on each selected member implies agreement after their union projector. -/
theorem finiteAction_eq {ι : Type w} (t : Finset ι) (U : ι → CompactOpen hX)
    (m n : M) (h : ∀ i ∈ t, action hX M (U i) m = action hX M (U i) n) :
    finiteAction hX M t U m = finiteAction hX M t U n := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have ht := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [finiteAction_insert, finiteAction_insert, ht, h i (Finset.mem_insert_self i t)]

/-- Finite gluing retains a comparison with every original cover member. -/
theorem finite_amalgamation {ι : Type w} (V : CompactOpen hX)
    (U : ι → CompactOpen hX) (hUV : ∀ i, (U i).obj ≤ V.obj)
    (s : ∀ i, Value hX M (U i)) (hs : Compatible (rawPresheaf hX M) U s)
    (t : Finset ι) :
    ∃ m : M, action hX M V m = m ∧
      ∀ j, action hX M (U j) m = finiteAction hX M t U (s j).val := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨0, (action hX M V).map_zero, fun j => by simp⟩
  | @insert i t hi ih =>
    obtain ⟨m, hm, hres⟩ := ih
    refine ⟨(s i).val + m - action hX M (U i) m, ?_, ?_⟩
    · rw [map_sub, map_add, value_fixed_of_le hX M (hUV i), hm,
        action_comm hX M V (U i), hm]
    · intro j
      rw [map_sub, map_add, compatible_action hX M hs j i,
        action_comm hX M (U j) (U i), hres j, finiteAction_insert]

/-- Genuine unique gluing for arbitrary independently indexed compact-open covers. -/
theorem familySheafCondition : FamilySheafCondition.{u,v,w} (rawPresheaf hX M) := by
  intro ι V U hU s hs
  change ∀ i, Value hX M (U i) at s
  obtain ⟨t, ht⟩ := (compact hX V).elim_finite_subcover
    (fun i => ((U i).obj : Set X)) (fun i => (U i).obj.isOpen) (by
      intro x hx
      obtain ⟨i, hi⟩ := hU.2 x hx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hsets : (⋃ i ∈ t, ((U i).obj : Set X)) = (V.obj : Set X) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp hx
      exact hU.1 i hi
    · exact ht
  have htest : finiteTest hX t U = test hX V := by
    ext x
    change (⋃ i ∈ t, ((U i).obj : Set X)).indicator (fun _ => (1 : ℂ)) x =
      (V.obj : Set X).indicator (fun _ => (1 : ℂ)) x
    rw [hsets]
  have ha (m : M) : finiteAction hX M t U m = action hX M V m := by
    change NonUnitalModuleCorner.originalAction (finiteTest hX t U) m =
      NonUnitalModuleCorner.originalAction (test hX V) m
    rw [htest]
  obtain ⟨m, hm, hres⟩ := finite_amalgamation hX M V U hU.1 s hs t
  have hall (i : ι) : action hX M (U i) m = (s i).val := by
    rw [hres i, ha]
    exact value_fixed_of_le hX M (hU.1 i) (s i)
  refine ⟨⟨m, hm⟩, fun i => Subtype.ext (hall i), ?_⟩
  intro y hy
  apply Subtype.ext
  calc
    y.val = action hX M V y.val := (value_fixed hX M y).symm
    _ = finiteAction hX M t U y.val := (ha _).symm
    _ = finiteAction hX M t U m := by
      apply finiteAction_eq
      intro i _
      exact (congrArg Subtype.val (hy i)).trans (hall i).symm
    _ = action hX M V m := ha _
    _ = m := hm

/-- The literal published set-cover sheaf condition, proved without an output hypothesis. -/
theorem sheafCondition : SheafCondition (rawPresheaf hX M) :=
  FamilySheafCondition.sheafCondition _ (familySheafCondition hX M)

/-- The actual basis sheaf at the unchanged module carrier universe. -/
def basisSheaf : BasisSheaf.{u,v} (compactOpenBasis hX) :=
  ⟨presheaf hX M, sheafCondition hX M⟩

/-- Explicit gluing retains the restriction equation on every original member. -/
theorem unique_gluing {ι : Type w} (V : CompactOpen hX) (U : ι → CompactOpen hX)
    (hU : FamilyCovers V U) (s : ∀ i, Value hX M (U i))
    (hs : Compatible (rawPresheaf hX M) U s) :
    ∃! t : Value hX M V, ∀ i, restrict hX M (hU.1 i) t = s i :=
  familySheafCondition hX M ι V U hU s hs

/-- Empty covers glue to the actual zero fixed vector. -/
theorem empty_gluing {ι : Type w} [IsEmpty ι]
    (V : CompactOpen hX) (U : ι → CompactOpen hX) (hU : FamilyCovers V U)
    (s : ∀ i, Value hX M (U i)) :
    ∃! t : Value hX M V, ∀ i, restrict hX M (hU.1 i) t = s i :=
  normalized_empty_gluing (presheaf hX M) hU s

/-- Every value on an empty space is the zero group. -/
theorem empty_space_value [IsEmpty X] (U : CompactOpen hX) (s : Value hX M U) :
    s = 0 := by
  apply empty_value_eq_zero hX M U
  apply bot_unique
  intro x
  exact isEmptyElim x

end Langlands.Sheaf.Renard.ProjectorBasisSheaf
