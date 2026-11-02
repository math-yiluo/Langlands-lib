import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleReducedLocus
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleZero

/-! # Invariance of symmetric tuple threshold opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]

/-- An action arrow relates the zeroth coordinates before and after a
permutation, even when its permutation varies across components. -/
def tuplePermutationRelationMap (n : ℕ) :
    (E.tuplePermutationAction n).relationScheme ⟶ E.R :=
  Sigma.desc fun g =>
    (E.tupleDistinctOpen n).ι ≫ E.tupleRelation n (g.down 0) 0

@[reassoc (attr := simp)]
theorem tuplePermutationRelationMap_t (n : ℕ) :
    E.tuplePermutationRelationMap n ≫ E.t =
      (E.tuplePermutationAction n).target ≫ E.tupleDistinctProjection n 0 := by
  apply Sigma.hom_ext
  intro g
  simp [tuplePermutationRelationMap, tupleDistinctProjection]

@[reassoc (attr := simp)]
theorem tuplePermutationRelationMap_s (n : ℕ) :
    E.tuplePermutationRelationMap n ≫ E.s =
      (E.tuplePermutationAction n).source ≫ E.tupleDistinctProjection n 0 := by
  apply Sigma.hom_ext
  intro g
  simp [tuplePermutationRelationMap, tupleDistinctProjection]

variable [IsAffine E.U] [IsAffine E.R]

/-- Ordered representatives of the same unordered tuple have related
zeroth-coordinate points in the original equivalence relation. -/
theorem tupleSymmetricMap_pointRel_of_eq (n : ℕ)
    {x y : E.tupleDistinctScheme n}
    (h : E.tupleSymmetricMap n x = E.tupleSymmetricMap n y) :
    E.PointRel (E.tupleDistinctProjection n 0 y) (E.tupleDistinctProjection n 0 x) := by
  obtain ⟨r, hrx, hry⟩ :=
    Scheme.exists_preimage_of_isPullback (E.tupleSymmetricMap_isPullback n) x y h
  refine ⟨E.tuplePermutationRelationMap n r, ?_, ?_⟩
  · change (E.tuplePermutationRelationMap n ≫ E.s) r = _
    rw [E.tuplePermutationRelationMap_s]
    change E.tupleDistinctProjection n 0 ((E.tuplePermutationAction n).source r) = _
    rw [hry]
  · change (E.tuplePermutationRelationMap n ≫ E.t) r = _
    rw [E.tuplePermutationRelationMap_t]
    change E.tupleDistinctProjection n 0 ((E.tuplePermutationAction n).target r) = _
    rw [hrx]

/-- Membership in a symmetric threshold can be tested on any ordered
representative and its zeroth coordinate. -/
theorem tupleSymmetricMap_mem_threshold_iff (n k : ℕ)
    (x : E.tupleDistinctScheme n) :
    E.tupleSymmetricMap n x ∈ E.tupleSymmetricThresholdOpen n k ↔
      E.tupleDistinctProjection n 0 x ∈ E.tupleThresholdOpen k := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact E.tupleThresholdOpen_invariant k
      (E.tupleSymmetricMap_pointRel_of_eq n hyx.symm) hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem tupleSymmetricThresholdOpen_preimage (n k : ℕ) :
    E.tupleSymmetricMap n ⁻¹ᵁ E.tupleSymmetricThresholdOpen n k =
      E.tupleDistinctProjection n 0 ⁻¹ᵁ E.tupleThresholdOpen k := by
  apply Opens.ext
  exact Set.ext (E.tupleSymmetricMap_mem_threshold_iff n k)

/-- Every symmetric cross arrow has its two endpoints in the same threshold. -/
theorem tupleSymmetricCross_threshold_iff (m n k : ℕ)
    (z : E.tupleSymmetricCrossScheme m n) :
    E.tupleSymmetricCrossLeft m n z ∈ E.tupleSymmetricThresholdOpen m k ↔
      E.tupleSymmetricCrossRight m n z ∈ E.tupleSymmetricThresholdOpen n k := by
  obtain ⟨w, rfl⟩ := (E.tupleSymmetricCrossMap m n).surjective z
  change (E.tupleSymmetricCrossMap m n ≫ E.tupleSymmetricCrossLeft m n) w ∈ _ ↔
    (E.tupleSymmetricCrossMap m n ≫ E.tupleSymmetricCrossRight m n) w ∈ _
  rw [E.tupleSymmetricCrossMap_left, E.tupleSymmetricCrossMap_right]
  change E.tupleSymmetricMap m (E.tupleCrossLeft m n w) ∈ _ ↔
    E.tupleSymmetricMap n (E.tupleCrossRight m n w) ∈ _
  rw [E.tupleSymmetricMap_mem_threshold_iff, E.tupleSymmetricMap_mem_threshold_iff]
  have ht : E.t (E.tupleCrossMap m n w) =
      E.tupleDistinctProjection m 0 (E.tupleCrossLeft m n w) :=
    congrArg (fun f => f w) (E.tupleCrossMap_t m n)
  have hs : E.s (E.tupleCrossMap m n w) =
      E.tupleDistinctProjection n 0 (E.tupleCrossRight m n w) :=
    congrArg (fun f => f w) (E.tupleCrossMap_s m n)
  have hrel : E.PointRel
      (E.tupleDistinctProjection n 0 (E.tupleCrossRight m n w))
      (E.tupleDistinctProjection m 0 (E.tupleCrossLeft m n w)) :=
    ⟨E.tupleCrossMap m n w, hs, ht⟩
  exact ⟨E.tupleThresholdOpen_invariant k (E.pointRel_symm hrel),
    E.tupleThresholdOpen_invariant k hrel⟩

theorem tupleSymmetricCross_threshold_preimage_eq (m n k : ℕ) :
    E.tupleSymmetricCrossLeft m n ⁻¹ᵁ E.tupleSymmetricThresholdOpen m k =
      E.tupleSymmetricCrossRight m n ⁻¹ᵁ E.tupleSymmetricThresholdOpen n k := by
  apply Opens.ext
  exact Set.ext (E.tupleSymmetricCross_threshold_iff m n k)

/-- The one-entry chart identifies symmetric thresholds with the original
invariant object thresholds. -/
theorem tupleSymmetricZeroIso_threshold_preimage (k : ℕ) :
    E.tupleSymmetricZeroIso.hom ⁻¹ᵁ E.tupleThresholdOpen k =
      E.tupleSymmetricThresholdOpen 0 k := by
  apply Opens.ext
  apply Set.ext
  intro z
  obtain ⟨x, rfl⟩ := (E.tupleSymmetricMap 0).surjective z
  change (E.tupleSymmetricMap 0 ≫ E.tupleSymmetricZeroIso.hom) x ∈
    E.tupleThresholdOpen k ↔
      E.tupleSymmetricMap 0 x ∈ E.tupleSymmetricThresholdOpen 0 k
  rw [E.tupleSymmetricMap_zeroIso_hom]
  exact (E.tupleSymmetricMap_mem_threshold_iff 0 k x).symm

/-- Only indices below the uniform tuple-length bound have nonempty charts. -/
theorem tupleSymmetricScheme_isEmpty (n : ℕ) (hn : E.tupleLengthBound ≤ n) :
    IsEmpty (E.tupleSymmetricScheme n) := by
  let := E.tupleDistinctScheme_isEmpty n hn
  exact ⟨fun x => by
    obtain ⟨y, _⟩ := (E.tupleSymmetricMap n).surjective x
    exact isEmptyElim y⟩

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
