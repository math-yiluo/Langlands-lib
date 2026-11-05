import Langlands.BruhatTits.RationalPoints.BoundedSubgroupNormKernel
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedTransport
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Bornology.Basic

/-!
# Operations on algebraically bounded sets of rational points

Elementary closure properties of KP algebraic boundedness (KP 2.2.1, Lemma 2.2.6):
monotonicity, finite unions, finite sets (packaged as the bornology
`algebraicBornology`), images under morphisms of affine
schemes, and, over a nonarchimedean local field, compact sets, products,
inverses and translates in the rational points of a finite-type affine group.
The group statements use the comparison between bounded sets and compact
closures in the canonical point topology.
-/

noncomputable section

universe u

open CategoryTheory Topology ValuativeRel
open _root_.AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.AlgebraicGeometry.PointTopology

section Basic

variable {F : Type u} [Field F] [ValuativeRel F]
  {X : Over (Spec (CommRingCat.of F))} [IsAffine X.left]

/-- Subsets of bounded sets are bounded. -/
theorem IsAlgebraicallyBounded.mono {S T : Set (RationalPoint F X)}
    (hT : IsAlgebraicallyBounded F X T) (h : S ⊆ T) :
    IsAlgebraicallyBounded F X S := by
  intro f
  obtain ⟨b, hb, hf⟩ := hT f
  exact ⟨b, hb, fun p hp => hf p (h hp)⟩

/-- The empty set is bounded. -/
theorem isAlgebraicallyBounded_empty : IsAlgebraicallyBounded F X ∅ :=
  fun _ => ⟨1, one_ne_zero, fun _ hp => hp.elim⟩

/-- A union of two bounded sets is bounded. -/
theorem IsAlgebraicallyBounded.union {S T : Set (RationalPoint F X)}
    (hS : IsAlgebraicallyBounded F X S) (hT : IsAlgebraicallyBounded F X T) :
    IsAlgebraicallyBounded F X (S ∪ T) := by
  intro f
  obtain ⟨b, hb, hbf⟩ := hS f
  obtain ⟨c, hc, hcf⟩ := hT f
  rcases vle_total b c with h | h
  · exact ⟨c, hc, fun p hp => hp.elim (fun hp => (hbf p hp).trans h) (hcf p)⟩
  · exact ⟨b, hb, fun p hp => hp.elim (hbf p) (fun hp => (hcf p hp).trans h)⟩

/-- A single rational point is bounded. -/
theorem isAlgebraicallyBounded_singleton (p : RationalPoint F X) :
    IsAlgebraicallyBounded F X {p} := by
  intro f
  by_cases h : rationalPointAlgebraHom F X p f = 0
  · refine ⟨1, one_ne_zero, fun q hq => ?_⟩
    rw [Set.mem_singleton_iff.mp hq, h]
    exact zero_vle 1
  · refine ⟨_, h, fun q hq => ?_⟩
    rw [Set.mem_singleton_iff.mp hq]

variable (F X) in
/-- The bornology on `X(F)` whose bounded sets are the algebraically bounded sets of
KP Definition 2.2.1. -/
@[instance_reducible]
def algebraicBornology : Bornology (RationalPoint F X) :=
  Bornology.ofBounded {S | IsAlgebraicallyBounded F X S} isAlgebraicallyBounded_empty
    (fun _ hT _ h => IsAlgebraicallyBounded.mono hT h) (fun _ hS _ hT => hS.union hT)
    isAlgebraicallyBounded_singleton

/-- The bounded sets of `algebraicBornology F X` are the algebraically bounded sets. -/
theorem isBounded_algebraicBornology_iff {S : Set (RationalPoint F X)} :
    @Bornology.IsBounded _ (algebraicBornology F X) S ↔ IsAlgebraicallyBounded F X S :=
  Bornology.isBounded_ofBounded_iff _

/-- A finite union of bounded sets is bounded. -/
theorem _root_.Set.Finite.isAlgebraicallyBounded_biUnion {I : Type*} {s : Set I}
    (hs : s.Finite) {S : I → Set (RationalPoint F X)}
    (h : ∀ i ∈ s, IsAlgebraicallyBounded F X (S i)) :
    IsAlgebraicallyBounded F X (⋃ i ∈ s, S i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa using (isAlgebraicallyBounded_empty : IsAlgebraicallyBounded F X ∅)
  | @insert a s _ _ ih =>
      rw [Set.biUnion_insert]
      exact (h a (Set.mem_insert a s)).union
        (ih fun i hi => h i (Set.mem_insert_of_mem a hi))

/-- A finite indexed union of bounded sets is bounded. -/
theorem isAlgebraicallyBounded_iUnion {I : Type*} [Finite I]
    {S : I → Set (RationalPoint F X)} (h : ∀ i, IsAlgebraicallyBounded F X (S i)) :
    IsAlgebraicallyBounded F X (⋃ i, S i) := by
  simpa using Set.finite_univ.isAlgebraicallyBounded_biUnion (fun i _ => h i)

/-- A finite set of rational points is bounded. -/
theorem _root_.Set.Finite.isAlgebraicallyBounded {S : Set (RationalPoint F X)}
    (hS : S.Finite) : IsAlgebraicallyBounded F X S := by
  simpa using Set.Finite.isAlgebraicallyBounded_biUnion hS (S := fun p => {p})
    (fun p _ => isAlgebraicallyBounded_singleton p)

/-- Images of bounded sets under morphisms of affine schemes are bounded:
each regular function on the target pulls back to one on the source. -/
theorem IsAlgebraicallyBounded.image {Y : Over (Spec (CommRingCat.of F))}
    [IsAffine Y.left] (f : X ⟶ Y) {S : Set (RationalPoint F X)}
    (hS : IsAlgebraicallyBounded F X S) :
    IsAlgebraicallyBounded F Y ((fun p => p ≫ f) '' S) := by
  intro a
  obtain ⟨b, hb, h⟩ := hS (affineCoordinatePullback F f a)
  refine ⟨b, hb, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [← rationalPointAlgebraHom_pullback]
  exact h p hp

/-- Images of bounded sets under homomorphisms of affine group schemes are bounded.
No finiteness or closed-immersion hypothesis is needed. -/
theorem IsAlgebraicallyBounded.image_rationalPointsMap
    {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine H.X.left]
    (j : H ⟶ G) {S : Set (rationalPoints H)}
    (hS : IsAlgebraicallyBounded F H.X S) :
    IsAlgebraicallyBounded F G.X (rationalPoints.map j '' S) :=
  hS.image j.hom.hom

end Basic

section LocalField

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

section Schemes

variable {X : Over (Spec (CommRingCat.of F))} [IsAffine X.left]

/-- Compact sets in the canonical point topology are bounded. -/
theorem isAlgebraicallyBounded_of_isCompact {S : Set (RationalPoint F X)}
    (hS : let : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
      IsCompact S) :
    IsAlgebraicallyBounded F X S := by
  let : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
  intro a
  let e₀ := (rationalPointHomeomorph F X).trans (affineSchemePointHomeomorph F X F)
  have hc : Continuous (fun p : RationalPoint F X => rationalPointAlgebraHom F X p a) :=
    (AlgPoint.continuous_eval a).comp e₀.continuous
  obtain ⟨b, hb, h⟩ := IsCompact.exists_valuative_bound (hS.image hc)
  exact ⟨b, hb, fun p hp => h _ ⟨p, hp, rfl⟩⟩

/-- For finite-type affine schemes, boundedness is compactness of the closure. -/
theorem isAlgebraicallyBounded_iff_isCompact_closure [LocallyOfFiniteType X.hom]
    {S : Set (RationalPoint F X)} :
    IsAlgebraicallyBounded F X S ↔
      (let _ : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X;
        IsCompact (closure S)) := by
  let : TopologicalSpace (RationalPoint F X) := rationalPointTopology F X
  exact ⟨fun h => h.isCompact_closure X,
    fun h => (isAlgebraicallyBounded_of_isCompact h).mono subset_closure⟩

end Schemes

section Groups

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

/-- KP Lemma 2.2.6 for products: a product of two bounded subsets of `G(F)` is bounded. -/
theorem IsAlgebraicallyBounded.mul {S T : Set (rationalPoints G)}
    (hS : IsAlgebraicallyBounded F G.X S) (hT : IsAlgebraicallyBounded F G.X T) :
    IsAlgebraicallyBounded F G.X (S * T) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  exact (isAlgebraicallyBounded_of_isCompact
    ((hS.isCompact_closure G.X).mul (hT.isCompact_closure G.X))).mono
    (Set.mul_subset_mul subset_closure subset_closure)

/-- The pointwise inverse of a bounded subset of `G(F)` is bounded. -/
theorem IsAlgebraicallyBounded.inv {S : Set (rationalPoints G)}
    (hS : IsAlgebraicallyBounded F G.X S) :
    IsAlgebraicallyBounded F G.X S⁻¹ := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  exact (isAlgebraicallyBounded_of_isCompact (hS.isCompact_closure G.X).inv).mono
    (Set.inv_subset_inv.mpr subset_closure)

/-- Left translates of bounded subsets of `G(F)` are bounded. -/
theorem IsAlgebraicallyBounded.smul_set {S : Set (rationalPoints G)}
    (hS : IsAlgebraicallyBounded F G.X S) (g : rationalPoints G) :
    IsAlgebraicallyBounded F G.X (g • S) := by
  refine ((isAlgebraicallyBounded_singleton g).mul hS).mono ?_
  rintro _ ⟨s, hs, rfl⟩
  exact Set.mul_mem_mul (Set.mem_singleton g) hs

/-- Right translates of bounded subsets of `G(F)` are bounded. -/
theorem IsAlgebraicallyBounded.mul_singleton {S : Set (rationalPoints G)}
    (hS : IsAlgebraicallyBounded F G.X S) (g : rationalPoints G) :
    IsAlgebraicallyBounded F G.X (S * {g}) :=
  hS.mul (isAlgebraicallyBounded_singleton g)

end Groups

end LocalField

end Langlands.AlgebraicGeometry.PointTopology
