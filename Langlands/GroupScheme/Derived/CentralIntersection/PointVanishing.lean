import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.JacobsonSpace

/-! # Global functions on reduced schemes over an algebraically closed field

Two elementary facts about global sections used by the central intersection finiteness proof:
a global function on a reduced scheme locally of finite type over an algebraically closed
field vanishes once it vanishes at every rational point, and an idempotent global function
on a connected reduced scheme is `0` or `1`. -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CentralIntersection

/-- On a reduced scheme `X` locally of finite type over an algebraically closed field `K`, a
global function whose pullback along every rational point vanishes is zero. -/
theorem eq_zero_of_forall_appTop_eq_zero {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsReduced X] (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p]
    (f : Γ(X, ⊤))
    (hf : ∀ q : Spec (CommRingCat.of K) ⟶ X, q ≫ p = 𝟙 _ → q.appTop f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  have hnonempty : (X.basicOpen f : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hne (TopologicalSpace.Opens.coe_eq_empty.mp h)
  obtain ⟨x, hxU, hx'⟩ :=
    nonempty_inter_closedPoints hnonempty (X.basicOpen f).isOpen.isLocallyClosed
  have hx : IsClosed ({x} : Set X) := hx'
  have hq := hf (pointOfClosedPoint p x hx) (pointOfClosedPoint_comp p x hx)
  obtain ⟨a⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have hmem : a ∈ (pointOfClosedPoint p x hx) ⁻¹ᵁ X.basicOpen f := by
    change pointOfClosedPoint p x hx a ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply]
    exact hxU
  rw [Scheme.preimage_basicOpen_top, hq, Scheme.basicOpen_zero] at hmem
  exact hmem

/-- On a connected reduced scheme, every idempotent global function is `0` or `1`. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem {X : Scheme.{u}} [IsReduced X]
    [ConnectedSpace X] {e : Γ(X, ⊤)} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hdisj : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, mul_sub, mul_one, he.eq, sub_self, Scheme.basicOpen_zero]
  have hcover : ∀ x : X, x ∈ X.basicOpen e ∨ x ∈ X.basicOpen (1 - e) := by
    intro x
    rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top]
    apply IsLocalRing.isUnit_or_isUnit_of_add_one
    rw [← map_add, add_sub_cancel, map_one]
  have hcompl : (X.basicOpen e : Set X)ᶜ = X.basicOpen (1 - e) := by
    ext x
    constructor
    · intro hx
      exact (hcover x).resolve_left hx
    · intro hx hx'
      have : x ∈ X.basicOpen e ⊓ X.basicOpen (1 - e) := ⟨hx', hx⟩
      rw [hdisj] at this
      exact this
  have hclopen : IsClopen (X.basicOpen e : Set X) := by
    refine ⟨?_, (X.basicOpen e).isOpen⟩
    rw [← isOpen_compl_iff, hcompl]
    exact (X.basicOpen (1 - e)).isOpen
  rcases isClopen_iff.mp hclopen with h | h
  · left
    rw [← basicOpen_eq_bot_iff]
    exact TopologicalSpace.Opens.coe_eq_empty.mp h
  · right
    have h' : (X.basicOpen (1 - e) : Set X) = ∅ := by
      rw [← hcompl, h, Set.compl_univ]
    have h0 : 1 - e = 0 := by
      rw [← basicOpen_eq_bot_iff]
      exact TopologicalSpace.Opens.coe_eq_empty.mp h'
    exact (sub_eq_zero.mp h0).symm

end Langlands.GroupScheme.CentralIntersection
