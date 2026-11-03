import Langlands.Group.RelativeWeylSolomonProof
import Mathlib.Algebra.BigOperators.Module

/-! # Signed sums of intrinsic Coxeter intersections

This is the finite additive assembly used after Aubert's equation (1.8).
It does not identify actual reductive-group intersections or functors.
-/

noncomputable section

universe uB uW uA

namespace Langlands.Group.RelativeWeylIndexing

open Classical
open scoped BigOperators

variable {B : Type uB} {W : Type uW} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
variable [Fintype B] [Fintype W]
variable {A : Type uA} [AddCommGroup A]

/-- The signed sum of values indexed by source-side Coxeter intersections,
over every standard subset and its minimal double-coset representatives. -/
def signedIntersectionSum (J : Finset B) (f : Finset B → A) : A :=
  ∑ I : Finset B, ((-1 : ℤ) ^ I.card) •
    ∑ w ∈ minimalReps cs I J, f (intersectionSubset cs I J w)

/-- Partitioning minimal representatives by the intrinsic intersection subset
recovers the already constructed intersection multiplicities. -/
theorem sum_minimalReps_intersectionSubset (I J : Finset B) (f : Finset B → A) :
    (∑ w ∈ minimalReps cs I J, f (intersectionSubset cs I J w)) =
      ∑ K ∈ J.powerset, (intersectionMultiplicity cs J I K : ℤ) • f K := by
  rw [← Finset.sum_fiberwise_of_maps_to'
    (g := intersectionSubset cs I J) (t := J.powerset)
    (fun w _ => Finset.mem_powerset.mpr (intersectionSubset_subset cs I J w)) f]
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℤ]
  congr 1
  unfold intersectionMultiplicity
  apply congrArg (fun s : Finset W => (s.card : ℤ))
  apply Finset.filter_congr
  intro w hw
  rw [standardIntersection_proof cs I J w ((mem_minimalReps cs I J w).mp hw)]
  exact ⟨congrArg (standardSubgroup cs), standardSubgroup_injective cs⟩

/-- Solomon cancellation holds with arbitrary values in an abelian group,
including integer-linear maps between exact Grothendieck groups. -/
theorem signedIntersectionSum_eq (J : Finset B) (f : Finset B → A) :
    signedIntersectionSum cs J f =
      ∑ K ∈ J.powerset, ((-1 : ℤ) ^ K.card) • f K := by
  unfold signedIntersectionSum
  simp_rw [sum_minimalReps_intersectionSubset, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K hK
  rw [← Finset.sum_smul,
    solomonCancellation_proof cs J K (Finset.mem_powerset.mp hK)]

omit [Fintype B] [Fintype W] in
/-- The ambient subsets contained in `J` are exactly the finite subsets of
the subtype `J`. The embedding preserves each cardinality and hence its sign. -/
theorem sum_powerset_eq_sum_subtype (J : Finset B) (f : Finset B → A) :
    (∑ K ∈ J.powerset, ((-1 : ℤ) ^ K.card) • f K) =
      ∑ K : Finset J, ((-1 : ℤ) ^ K.card) •
        f (K.map (Function.Embedding.subtype (· ∈ J))) := by
  symm
  refine Finset.sum_bij
    (fun K _ => K.map (Function.Embedding.subtype (· ∈ J))) ?_ ?_ ?_ ?_
  · intro K _
    exact Finset.mem_powerset.mpr fun b hb => Finset.property_of_mem_map_subtype K hb
  · intro K _ L _ h
    exact Finset.map_injective (Function.Embedding.subtype (· ∈ J)) h
  · intro K hK
    exact ⟨K.subtype (· ∈ J), Finset.mem_univ _,
      Finset.subtype_map_of_mem (Finset.mem_powerset.mp hK)⟩
  · intro K _
    rw [Finset.card_map]

/-- The additive assembly lands in the literal finite-subtype indexing used
by the alternating operator of a standard Levi. -/
theorem signedIntersectionSum_eq_sum_subtype (J : Finset B) (f : Finset B → A) :
    signedIntersectionSum cs J f =
      ∑ K : Finset J, ((-1 : ℤ) ^ K.card) •
        f (K.map (Function.Embedding.subtype (· ∈ J))) := by
  rw [signedIntersectionSum_eq, sum_powerset_eq_sum_subtype]

end Langlands.Group.RelativeWeylIndexing
