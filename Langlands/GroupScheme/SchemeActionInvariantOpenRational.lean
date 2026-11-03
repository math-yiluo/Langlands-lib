import Langlands.GroupScheme.SchemeActionInvariantOpen
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Detecting invariant opens on rational points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Opens of a locally finite type scheme over an algebraically closed field
are determined by their membership at rational points. -/
theorem opens_eq_of_rationalPoints
    {X : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType X.hom]
    {V W : X.left.Opens}
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
      x.left (IsLocalRing.closedPoint k) ∈ V ↔
        x.left (IsLocalRing.closedPoint k) ∈ W) : V = W := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hclosed : ∀ x ∈ closedPoints X.left, x ∈ V ↔ x ∈ W := by
    intro x hx
    let p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
    have hp : p.left (IsLocalRing.closedPoint k) = x :=
      pointOfClosedPoint_apply _ _ _ _
    simpa only [hp] using h p
  have hsub : ∀ (A B : X.left.Opens),
      (∀ x ∈ closedPoints X.left, x ∈ A → x ∈ B) → A ≤ B := by
    intro A B hAB x hx
    by_contra hxB
    obtain ⟨y, ⟨hyA, hyB⟩, hyc⟩ :=
      nonempty_inter_closedPoints (Z := (A : Set X.left) ∩ (B : Set X.left)ᶜ)
        ⟨x, hx, hxB⟩ (A.isOpen.isLocallyClosed.inter B.isOpen.isClosed_compl.isLocallyClosed)
    exact hyB (hAB y hyc hyA)
  exact le_antisymm (hsub V W (fun x hx => (hclosed x hx).mp))
    (hsub W V (fun x hx => (hclosed x hx).mpr))

namespace SchemeAction

variable {H : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction H X)

/-- Membership in the open is preserved and reflected on rational action points. -/
def RationalOpenMembership (V : X.left.Opens) : Prop :=
  ∀ (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X),
    (a.act h x).left (IsLocalRing.closedPoint k) ∈ V ↔
      x.left (IsLocalRing.closedPoint k) ∈ V

/-- For locally finite type group and target, rational membership invariance is
exactly equality of the action and projection inverse-image opens. -/
theorem isInvariantOpen_iff_rationalOpenMembership
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType X.hom]
    (V : X.left.Opens) : a.IsInvariantOpen V ↔ a.RationalOpenMembership V := by
  constructor
  · intro hV h x
    exact hV.mem_act_iff h x (IsLocalRing.closedPoint k)
  · intro hV
    have : LocallyOfFiniteType (H.X ⊗ X).hom := by
      change LocallyOfFiniteType (Limits.pullback.fst H.X.hom X.hom ≫ H.X.hom)
      infer_instance
    apply opens_eq_of_rationalPoints
    intro p
    have hp : a.act (p ≫ fst H.X X) (p ≫ snd H.X X) = p ≫ a.hom := by
      rw [act, ← comp_lift, lift_fst_snd, Category.comp_id]
    have h := hV (p ≫ fst H.X X) (p ≫ snd H.X X)
    rw [hp] at h
    exact h

end SchemeAction

end Langlands.GroupScheme
