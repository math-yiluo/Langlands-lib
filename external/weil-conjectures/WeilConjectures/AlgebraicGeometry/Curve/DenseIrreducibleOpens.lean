/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Dense disjoint irreducible opens in a curve -/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Set

namespace AlgebraicGeometry.IsCurve

/-- A dense open of a curve can be shrunk to a finite disjoint union of irreducible opens.
Source: Stacks Project, Theorem 03SC, proof, third paragraph
(blueprint: lemma-removing-finitely-many-points--1).

Proof: A finite-type scheme over a field is Noetherian and has finitely many irreducible
components C_a, each with a generic point. A dense open V contains every generic point:
its intersection with the open part of C_a outside all other components is nonempty,
and an open containing a specialization of the generic point contains that generic point.
Remove from V the union of the intersections of distinct components. These intersections
are closed, contain no generic point, and have dimension at most zero, since every component
has dimension at most one. The remainder W is open and contains every generic point, hence
is dense. Its intersections U_a with the components are nonempty irreducible opens, pairwise
disjoint, and cover W. Each is closed in W as well, since its complement is a finite union
of the other opens. Thus the connected component in W of a point of U_a is exactly U_a:
irreducibility implies connectedness, and a connected set cannot cross a clopen partition.
The complement of W is closed and contains no generic point. Every point in it is closed,
since a non-generic point of a component of dimension at most one has zero-dimensional
irreducible closure. Noetherianity makes this complement a finite set of closed points,
so its topological Krull dimension is at most zero. If X is empty, take n = 0; all density
and component conditions are vacuous and the empty complement has dimension bottom. -/
theorem exists_dense_irreducible_opens {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (V : X.Opens) (hV : Dense (V : Set X)) :
    ∃ (n : ℕ) (U : Fin n → X.Opens),
      (∀ a, U a ≤ V) ∧ Dense (⋃ a, (U a : Set X)) ∧
      Pairwise (fun a b ↦ Disjoint (U a : Set X) (U b)) ∧
      (∀ a, IsIrreducible (U a : Set X)) ∧
      topologicalKrullDim ↥(⋃ a, (U a : Set X))ᶜ ≤ 0 ∧
      (∀ x ∈ (⋃ a, (U a : Set X)),
        IsIrreducible (connectedComponentIn (⋃ a, (U a : Set X)) x)) := by
  classical
  have := isNoetherian_of_locallyOfFiniteType f
  have : NoetherianSpace X := inferInstance
  let I := irreducibleComponents X
  have : Finite I := NoetherianSpace.finite_irreducibleComponents
  let : Fintype I := Fintype.ofFinite I
  let O : I → X.Opens := fun a ↦
    ⟨(⋃₀ (irreducibleComponents X \ {a.1}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        (fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1)⟩
  have hOcl (a : I) : closure (O a : Set X) = a.1 :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents a.1 a.2
  have hOsub (a : I) : (O a : Set X) ⊆ a.1 := by
    rw [← hOcl a]
    exact subset_closure
  have hOne (a : I) : (O a : Set X).Nonempty := by
    by_contra! he
    have : a.1 = ∅ := by rw [← hOcl a, he, closure_empty]
    exact a.2.1.nonempty.ne_empty this
  let T : I → X.Opens := fun a ↦ V ⊓ O a
  have hTne (a : I) : (T a : Set X).Nonempty := by
    simpa only [T, TopologicalSpace.Opens.coe_inf, Set.inter_comm] using
      hV.inter_open_nonempty (O a : Set X) (O a).isOpen (hOne a)
  have hTsub (a : I) : (T a : Set X) ⊆ a.1 :=
    fun _ hx ↦ hOsub a hx.2
  have hTirr (a : I) : IsIrreducible (T a : Set X) :=
    a.2.1.2.subset_irreducible (hTne a) (T a).isOpen subset_rfl (hTsub a)
  have hTcl (a : I) : closure (T a : Set X) = a.1 := by
    apply subset_antisymm
    · exact closure_minimal (hTsub a) (isClosed_of_mem_irreducibleComponents a.1 a.2)
    · exact subset_closure_inter_of_isPreirreducible_of_isOpen a.2.1.2 (T a).isOpen
        (by simpa only [inter_eq_right.mpr (hTsub a)] using hTne a)
        |>.trans (by rw [inter_eq_right.mpr (hTsub a)])
  have hTdisj : Pairwise (fun a b ↦ Disjoint (T a : Set X) (T b)) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hxa.2 (Set.mem_sUnion_of_mem (hTsub b hxb)
      ⟨b.2, by simpa only [Set.mem_singleton_iff] using
        (show b.1 ≠ a.1 from fun he ↦ hab (Subtype.ext he.symm))⟩)
  have hdense : Dense (⋃ a, (T a : Set X)) := by
    intro x
    let a : I := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hx : x ∈ closure (T a : Set X) := by
      rw [hTcl a]
      exact mem_irreducibleComponent
    exact closure_mono (Set.subset_iUnion (fun a ↦ (T a : Set X)) a) hx
  have hdim : topologicalKrullDim ↥(⋃ a, (T a : Set X))ᶜ ≤ 0 := by
    have hclosed : IsClosed (⋃ a, (T a : Set X))ᶜ :=
      (isOpen_iUnion (fun a ↦ (T a).isOpen)).isClosed_compl
    have hgen : ∀ w ∈ (⋃ a, (T a : Set X))ᶜ,
        ∃ z ∈ (Set.univ : Set X), z ⤳ w ∧ z ∉ (⋃ a, (T a : Set X))ᶜ := by
      intro w _
      let a : I := ⟨irreducibleComponent w, irreducibleComponent_mem_irreducibleComponents w⟩
      obtain ⟨z, hz⟩ := QuasiSober.sober a.2.1
        (isClosed_of_mem_irreducibleComponents a.1 a.2)
      obtain ⟨y, hy⟩ := hTne a
      have hzT : z ∈ (T a : Set X) := (hz.specializes (hTsub a hy)).mem_open (T a).isOpen hy
      exact ⟨z, Set.mem_univ _, hz.specializes mem_irreducibleComponent,
        not_not.mpr (Set.mem_iUnion.mpr ⟨a, hzT⟩)⟩
    have hdrop : topologicalKrullDim ↥(⋃ a, (T a : Set X))ᶜ < (1 : ℕ) :=
      topologicalKrullDim_lt_of_forall_exists_specializes isClosed_univ hclosed
        (Set.subset_univ _) hgen (d := 1)
        (lt_of_le_of_lt ((topologicalKrullDim_subspace_le X Set.univ).trans
          (IsCurve.krullDim_le_one (f := f))) (by decide))
    exact ENat.WithBot.lt_add_one_iff.mp (by simpa using hdrop)
  have hcomp : ∀ x ∈ (⋃ a, (T a : Set X)),
      IsIrreducible (connectedComponentIn (⋃ a, (T a : Set X)) x) := by
    intro x hx
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
    let B : Set X := ⋃ b : {b : I // b ≠ a}, (T b.1 : Set X)
    have hB : IsOpen B := isOpen_iUnion (fun b ↦ (T b.1).isOpen)
    have hAB : Disjoint (T a : Set X) B := by
      rw [Set.disjoint_left]
      intro y hya hyB
      obtain ⟨b, hyb⟩ := Set.mem_iUnion.mp hyB
      exact Set.disjoint_left.mp (hTdisj b.2.symm) hya hyb
    have hcover : (⋃ b, (T b : Set X)) ⊆ (T a : Set X) ∪ B := by
      intro y hy
      obtain ⟨b, hyb⟩ := Set.mem_iUnion.mp hy
      by_cases hba : b = a
      · exact Or.inl (hba ▸ hyb)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨b, hba⟩, hyb⟩)
    have heq : connectedComponentIn (⋃ b, (T b : Set X)) x = (T a : Set X) := by
      apply subset_antisymm
      · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
          (T a).isOpen hB hAB ((connectedComponentIn_subset _ _).trans hcover)
          ⟨x, mem_connectedComponentIn hx, hxa⟩
      · exact (hTirr a).2.isPreconnected.subset_connectedComponentIn hxa
          (Set.subset_iUnion (fun b ↦ (T b : Set X)) a)
    rw [heq]
    exact hTirr a
  let e := (Fintype.equivFin I).symm
  have heq : (⋃ a, (T (e a) : Set X)) = ⋃ a, (T a : Set X) :=
    e.surjective.iUnion_comp (fun a ↦ (T a : Set X))
  refine ⟨Fintype.card I, fun a ↦ T (e a), fun a ↦ inf_le_left, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [heq] using hdense
  · exact hTdisj.comp_of_injective e.injective
  · exact fun a ↦ hTirr (e a)
  · change topologicalKrullDim ↥(⋃ a, (T (e a) : Set X))ᶜ ≤ 0
    rw [heq]
    exact hdim
  · simpa only [heq] using hcomp

end AlgebraicGeometry.IsCurve
