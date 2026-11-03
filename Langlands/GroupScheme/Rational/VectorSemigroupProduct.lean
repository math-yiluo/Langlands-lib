import Langlands.GroupScheme.Rational.VectorCoordinateLieSupport

/-! # Exact ordered semigroup products for actual linear vector actions -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

namespace HomogeneousVectorCoordinates

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V}
    (q : HomogeneousVectorCoordinates b)

/-- The coordinate indices whose actual labels belong to a specified weight block. -/
def weightBlockIndices {n : ℕ} (Ψ : Fin n → Set (characterLattice S)) :
    Fin n → Set (Fin q.dimension) :=
  fun r => {i | q.weight i ∈ Ψ r}

omit [IsAffineHom V.X.hom] in
/-- Allowing every coordinate gives the full actual group functor. -/
theorem coordinateSubgroup_univ_eq_top :
    vectorCoordinateSubgroup q.coordinates q.naturality Set.univ = ⊤ := by
  ext T v
  simp [vectorCoordinateSubgroup]

/-- The full original-action Lie support consists of exactly the occurring labels. -/
theorem actionWeightSupport_top (hS : IsSplitTorus S.toGrp) :
    actionWeightSupport b ⊤ = Set.range q.weight := by
  calc
    actionWeightSupport b ⊤ =
        actionWeightSupport b
          (vectorCoordinateSubgroup q.coordinates q.naturality Set.univ) := by
      rw [q.coordinateSubgroup_univ_eq_top]
    _ = q.weight '' Set.univ := q.actionWeightSupport_coordinateSubgroup hS _
    _ = Set.range q.weight := Set.image_univ

/-- A disjoint covering of all actual weights partitions the actual coordinate indices. -/
theorem weightBlockIndices_partition (hS : IsSplitTorus S.toGrp)
    {n : ℕ} (Ψ : Fin n → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤)
    (hdisj : ∀ r s, r ≠ s → Disjoint (Ψ r) (Ψ s)) :
    ∀ i, ∃! r, i ∈ q.weightBlockIndices Ψ r := by
  intro i
  have hi : q.weight i ∈ actionWeightSupport b ⊤ := by
    rw [q.actionWeightSupport_top hS]
    exact ⟨i, rfl⟩
  rw [← hcover] at hi
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hi
  refine ⟨r, hr, ?_⟩
  intro s hs
  by_contra hsr
  exact (Set.disjoint_left.mp (hdisj s r hsr)) hs hr

/-- Exact block-versus-generated-semigroup exclusion prevents any other occurring
coordinate label from entering a block's positive semigroup. -/
theorem mem_closure_iff_mem_block (hS : IsSplitTorus S.toGrp)
    {n : ℕ} (Ψ : Fin n → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤)
    (hcross : ∀ r s, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S)))
    (r : Fin n) (i : Fin q.dimension) :
    q.weight i ∈ AddSubsemigroup.closure (Ψ r) ↔
      i ∈ q.weightBlockIndices Ψ r := by
  constructor
  · intro hi
    have hlabel : q.weight i ∈ actionWeightSupport b ⊤ := by
      rw [q.actionWeightSupport_top hS]
      exact ⟨i, rfl⟩
    rw [← hcover] at hlabel
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hlabel
    by_cases hsr : s = r
    · subst s
      exact hs
    · exact False.elim ((Set.disjoint_left.mp (hcross s r hsr)) hs hi)
  · intro hi
    exact AddSubsemigroup.subset_closure hi

/-- The exact generated block is the subgroup obtained by retaining just its
original weight-block coordinates, under the explicit support comparison. -/
theorem semigroupSubgroup_closure_eq_block
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hS : IsSplitTorus S.toGrp)
    {n : ℕ} (Ψ : Fin n → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤)
    (hcross : ∀ r s, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S)))
    (r : Fin n) :
    semigroupSubgroup b (AddSubsemigroup.closure (Ψ r)) =
      vectorCoordinateSubgroup q.coordinates q.naturality (q.weightBlockIndices Ψ r) := by
  rw [q.semigroupSubgroup_eq_coordinateSubgroup hContain hS]
  congr 1
  ext i
  exact q.mem_closure_iff_mem_block hS Ψ hcover hcross r i

include q in
/-- The exact CGP hypotheses give smooth connected closed semigroup factors
and the original ordered-multiplication isomorphism for homogeneous vector actions. -/
theorem semigroupOrderedProduct
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hS : IsSplitTorus S.toGrp)
    (n : ℕ) (Ψ : Fin n → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤)
    (hdisj : ∀ r s, r ≠ s → Disjoint (Ψ r) (Ψ s))
    (hcross : ∀ r s, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) :
    ∃ (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ V),
      (∀ r, (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))).IsRepresentedBy (j r) ∧
        IsClosedSubgroup (j r) ∧ Smooth (H r).X.hom ∧ ConnectedSpace (H r).X.left) ∧
      IsIso (orderedMultiplication j) := by
  classical
  have hF (r : Fin n) :
      IsSmoothConnectedClosed (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))) := by
    rw [q.semigroupSubgroup_closure_eq_block hContain hS Ψ hcover hcross]
    exact isSmoothConnectedClosed_vectorCoordinateSubgroup q.coordinates q.naturality _
  choose H j hj hclosed hsmooth hconn using hF
  refine ⟨H, j, fun r => ⟨hj r, hclosed r, hsmooth r, hconn r⟩, ?_⟩
  apply isIso_orderedMultiplication_vectorCoordinates q.coordinates q.naturality
    (q.weightBlockIndices Ψ) (q.weightBlockIndices_partition hS Ψ hcover hdisj) j
  intro r
  rw [← q.semigroupSubgroup_closure_eq_block hContain hS Ψ hcover hcross]
  exact hj r

end HomogeneousVectorCoordinates

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom V.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V} {d : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))}

/-- The vector case for any supplied original scalar-linear coordinates,
with no chosen homogeneous basis as an additional input. -/
theorem IsLinearVectorCoordinates.semigroupOrderedProduct
    (hb : IsLinearVectorCoordinates b e)
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hS : IsSplitTorus S.toGrp)
    (n : ℕ) (Ψ : Fin n → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = actionWeightSupport b ⊤)
    (hdisj : ∀ r s, r ≠ s → Disjoint (Ψ r) (Ψ s))
    (hcross : ∀ r s, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) :
    ∃ (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ r, H r ⟶ V),
      (∀ r, (semigroupSubgroup b (AddSubsemigroup.closure (Ψ r))).IsRepresentedBy (j r) ∧
        IsClosedSubgroup (j r) ∧ Smooth (H r).X.hom ∧ ConnectedSpace (H r).X.left) ∧
      IsIso (orderedMultiplication j) :=
  (hb.homogeneousCoordinates hS).semigroupOrderedProduct hContain hS n Ψ hcover hdisj hcross

end Langlands.GroupScheme.RelativeRoot
