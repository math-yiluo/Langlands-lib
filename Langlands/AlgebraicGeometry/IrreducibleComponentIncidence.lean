import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Connectedness and the intersections of actual irreducible components -/

noncomputable section

universe u v w z

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ComponentIncidence

variable {A : Type u} [TopologicalSpace A] {ι : Type v}

/-- Incidence is actual nonempty intersection, with no distinctness requirement. -/
def intersectionRelation (s : ι → Set A) (i j : ι) : Prop :=
  (s i ∩ s j).Nonempty

/-- The intersection relation has a vertex and joins every pair by a finite chain. -/
def IntersectionChainConnected (s : ι → Set A) : Prop :=
  Nonempty ι ∧ ∀ i j, Relation.ReflTransGen (intersectionRelation s) i j

/-- A connected union of finitely many nonempty closed sets has connected incidence.
The individual closed sets need not themselves be connected in this direction. -/
theorem intersectionChainConnected_of_isConnected_iUnion
    [Finite ι] (s : ι → Set A) (hclosed : ∀ i, IsClosed (s i))
    (hne : ∀ i, (s i).Nonempty) (hconn : IsConnected (⋃ i, s i)) :
    IntersectionChainConnected s := by
  classical
  have hι : Nonempty ι := by
    obtain ⟨x, hx⟩ := hconn.nonempty
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
    exact ⟨i⟩
  refine ⟨hι, ?_⟩
  intro i j
  by_contra hij
  let T : Set ι := {k | Relation.ReflTransGen (intersectionRelation s) i k}
  let U : Set A := ⋃ k ∈ T, s k
  let V : Set A := ⋃ k ∈ Tᶜ, s k
  have hU : IsClosed U :=
    (Set.toFinite T).isClosed_biUnion fun k _ => hclosed k
  have hV : IsClosed V :=
    (Set.toFinite Tᶜ).isClosed_biUnion fun k _ => hclosed k
  have hcover : (⋃ k, s k) ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    by_cases hk : k ∈ T
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)
  obtain ⟨x, hxi⟩ := hne i
  obtain ⟨y, hyj⟩ := hne j
  have hiT : i ∈ T := Relation.ReflTransGen.refl
  have hjT : j ∉ T := hij
  have hxU : ((⋃ k, s k) ∩ U).Nonempty :=
    ⟨x, Set.mem_iUnion.mpr ⟨i, hxi⟩, Set.mem_iUnion₂.mpr ⟨i, hiT, hxi⟩⟩
  have hyV : ((⋃ k, s k) ∩ V).Nonempty :=
    ⟨y, Set.mem_iUnion.mpr ⟨j, hyj⟩, Set.mem_iUnion₂.mpr ⟨j, hjT, hyj⟩⟩
  obtain ⟨z, _, hzU, hzV⟩ :=
    isPreconnected_closed_iff.mp hconn.isPreconnected U V hU hV hcover hxU hyV
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hzU
  obtain ⟨l, hl, hzl⟩ := Set.mem_iUnion₂.mp hzV
  exact hl (hk.tail ⟨z, hzk, hzl⟩)

/-- For a finite closed connected cover, topology and the intersection relation
give the same connectedness condition, including nonemptiness. -/
theorem isConnected_iUnion_iff_intersectionChainConnected
    [Finite ι] (s : ι → Set A) (hclosed : ∀ i, IsClosed (s i))
    (hconn : ∀ i, IsConnected (s i)) :
    IsConnected (⋃ i, s i) ↔ IntersectionChainConnected s := by
  constructor
  · exact intersectionChainConnected_of_isConnected_iUnion s hclosed
      (fun i => (hconn i).nonempty)
  · rintro ⟨hι, hchain⟩
    let := hι
    exact IsConnected.iUnion_of_reflTransGen hconn hchain

omit [TopologicalSpace A] in
/-- Only the intersection pattern, rather than a map between the ambient spaces,
is needed to transport finite-chain connectedness. -/
theorem intersectionChainConnected_congr
    {B : Type w} {κ : Type z}
    (s : ι → Set A) (t : κ → Set B) (e : ι ≃ κ)
    (h : ∀ i j, (s i ∩ s j).Nonempty ↔ (t (e i) ∩ t (e j)).Nonempty) :
    IntersectionChainConnected s ↔ IntersectionChainConnected t := by
  constructor
  · rintro ⟨hι, hc⟩
    refine ⟨hι.map e, ?_⟩
    intro i j
    have hh : Relation.ReflTransGen (intersectionRelation t)
        (e (e.symm i)) (e (e.symm j)) :=
      (hc (e.symm i) (e.symm j)).lift e (p := intersectionRelation t)
        (fun k l hkl => (h k l).mp hkl)
    simpa only [Equiv.apply_symm_apply] using hh
  · rintro ⟨hκ, hc⟩
    refine ⟨hκ.map e.symm, ?_⟩
    intro i j
    have hstep : ∀ k l, intersectionRelation t k l →
        intersectionRelation s (e.symm k) (e.symm l) := by
      intro k l hkl
      apply (h (e.symm k) (e.symm l)).mpr
      change (t k ∩ t l).Nonempty at hkl
      simpa using hkl
    have hh : Relation.ReflTransGen (intersectionRelation s)
        (e.symm (e i)) (e.symm (e j)) :=
      (hc (e i) (e j)).lift e.symm hstep
    simpa only [Equiv.symm_apply_apply] using hh

/-- The actual irreducible components, regarded as subsets of the space. -/
def componentSets (A : Type u) [TopologicalSpace A] :
    irreducibleComponents A → Set A := Subtype.val

/-- Incidence of the actual irreducible components of the space. -/
def irreducibleComponentIncidence (A : Type u) [TopologicalSpace A] :
    irreducibleComponents A → irreducibleComponents A → Prop :=
  intersectionRelation (componentSets A)

/-- The incidence relation of actual components is inhabited and chain connected. -/
def IrreducibleComponentChainsConnected (A : Type u) [TopologicalSpace A] : Prop :=
  IntersectionChainConnected (componentSets A)

theorem iUnion_componentSets (A : Type u) [TopologicalSpace A] :
    (⋃ C : irreducibleComponents A, componentSets A C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr
    ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
      mem_irreducibleComponent⟩

/-- Finitely many actual irreducible components detect connectedness exactly. -/
theorem connectedSpace_iff_componentChains
    (hfinite : (irreducibleComponents A).Finite) :
    ConnectedSpace A ↔ IrreducibleComponentChainsConnected A := by
  let := hfinite.to_subtype
  rw [connectedSpace_iff_univ, ← iUnion_componentSets A]
  exact isConnected_iUnion_iff_intersectionChainConnected (componentSets A)
    (fun C => isClosed_of_mem_irreducibleComponents C.val C.property)
    (fun C => C.property.1.isConnected)

/-- In particular the comparison holds for every Noetherian topological space. -/
theorem connectedSpace_iff_componentChains_of_noetherian [NoetherianSpace A] :
    ConnectedSpace A ↔ IrreducibleComponentChainsConnected A :=
  connectedSpace_iff_componentChains NoetherianSpace.finite_irreducibleComponents

/-- Equal incidence patterns on actual components preserve connectedness. -/
theorem connectedSpace_iff_of_componentIncidenceEquiv
    {B : Type w} [TopologicalSpace B]
    (hA : (irreducibleComponents A).Finite) (hB : (irreducibleComponents B).Finite)
    (e : irreducibleComponents A ≃ irreducibleComponents B)
    (h : ∀ C D, irreducibleComponentIncidence A C D ↔
      irreducibleComponentIncidence B (e C) (e D)) :
    ConnectedSpace A ↔ ConnectedSpace B :=
  (connectedSpace_iff_componentChains hA).trans
    ((intersectionChainConnected_congr (componentSets A) (componentSets B) e h).trans
      (connectedSpace_iff_componentChains hB).symm)

/-- The exact component-chain reformulation on all actual field base changes of
a finite-type morphism. This does not spread the components or their incidence. -/
theorem geometricallyConnected_iff_componentChains
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] :
    GeometricallyConnected f ↔
      ∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ Y),
        IrreducibleComponentChainsConnected (pullback f y : Scheme.{u}) := by
  rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ y
    let : IsNoetherian (pullback f y) :=
      { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
    exact connectedSpace_iff_componentChains_of_noetherian.mp (h K y)
  · intro h K _ y
    let : IsNoetherian (pullback f y) :=
      { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
    exact connectedSpace_iff_componentChains_of_noetherian.mpr (h K y)

end Langlands.AlgebraicGeometry.ComponentIncidence
