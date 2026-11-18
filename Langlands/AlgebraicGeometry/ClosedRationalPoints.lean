import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Closed points and rational points over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.ClosedRationalPoints

variable {k : Type u} [Field k]

/-- Every nonempty open subset of a scheme locally of finite type over a field contains a
closed point. -/
theorem exists_isClosed_mem {X : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) :
    ∃ x ∈ U, IsClosed ({x} : Set X.left) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, hxU, hx⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  exact ⟨x, hxU, hx⟩

variable [IsAlgClosed k]

/-- Over an algebraically closed field, every closed point is the image of a rational
point. -/
theorem exists_rationalPoint_of_isClosed {X : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] (z : X.left) (hz : IsClosed ({z} : Set X.left)) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
      x.left (IsLocalRing.closedPoint k) = z :=
  ⟨Over.homMk (pointOfClosedPoint X.hom z hz) (by simp), pointOfClosedPoint_apply _ _ _ _⟩

/-- Over an algebraically closed field, every nonempty open subset of a scheme locally of
finite type contains the image of a rational point. -/
theorem exists_rationalPoint_mem {X : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) (hU : (U : Set X.left).Nonempty) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
      x.left (IsLocalRing.closedPoint k) ∈ U := by
  obtain ⟨z, hzU, hz⟩ := exists_isClosed_mem U hU
  obtain ⟨x, hx⟩ := exists_rationalPoint_of_isClosed z hz
  exact ⟨x, hx ▸ hzU⟩

/-- The underlying point of a rational point is closed. -/
theorem isClosed_rationalPoint {X : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType X.hom]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    IsClosed ({x.left (IsLocalRing.closedPoint k)} : Set X.left) :=
  ((pointEquivClosedPoint X.hom) ⟨x.left, Over.w x⟩).2

/-- **Jacobson subset lemma.** Over an algebraically closed field, a locally closed subset
whose only rational point is `z` is contained in the underlying point of `z`. -/
theorem subset_singleton_of_rationalPoints {X : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] {Z : Set X.left} (hZ : IsLocallyClosed Z)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X)
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
      x.left (IsLocalRing.closedPoint k) ∈ Z → x = z) :
    Z ⊆ {z.left (IsLocalRing.closedPoint k)} := by
  intro y hy
  by_contra hne
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hZ' : IsLocallyClosed (Z ∩ {z.left (IsLocalRing.closedPoint k)}ᶜ) :=
    hZ.inter (isClosed_rationalPoint z).isOpen_compl.isLocallyClosed
  have hne' : (Z ∩ {z.left (IsLocalRing.closedPoint k)}ᶜ).Nonempty := ⟨y, hy, hne⟩
  obtain ⟨x, ⟨hxZ, hxne⟩, hx⟩ := nonempty_inter_closedPoints hne' hZ'
  obtain ⟨x', hx'⟩ := exists_rationalPoint_of_isClosed x hx
  apply hxne
  rw [← hx', h x' (hx' ▸ hxZ)]
  rfl

end Langlands.AlgebraicGeometry.ClosedRationalPoints
