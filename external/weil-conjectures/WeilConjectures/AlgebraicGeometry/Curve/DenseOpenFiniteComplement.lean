/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # The complement of a dense open in a curve

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 2 (normalization).
(blueprint: lem-sc-dense-open-finite-complement)
-/

@[expose] public section

universe u

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.IsCurve

/-- The complement of a dense open in a curve over an algebraically closed field is a finite
set of closed points with separably closed residue fields.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 2 (normalization).
(blueprint: lem-sc-dense-open-finite-complement)

Proof: The curve is Noetherian because it is finite type over a field. For every
irreducible component Z, the complement W of all the other components is open and
has closure Z. Thus W is nonempty and density forces V to meet W, hence Z. The
subspace Z is irreducible and has dimension at most one. Its nonempty open V ∩ Z
therefore has closed points as its complement, by the dimension-one specialization
chain argument. For x outside V, apply this to a component containing x. Since Z
is closed in C, the singleton {x} is closed in C. The closed complement of V is then
finite by the Noetherian closed-points finiteness theorem. Finally the residue field
of each closed point is isomorphic to the algebraically closed base field by the
Nullstellensatz, hence is algebraically closed and separably closed. The empty curve
and the empty complement satisfy all three clauses vacuously. -/
theorem dense_open_finite_complement {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (V : C.Opens) (hV : Dense (V : Set C)) :
    (V : Set C)ᶜ.Finite ∧ (∀ x ∉ V, IsClosed ({x} : Set C)) ∧
      (∀ x ∉ V, IsSepClosed (C.residueField x)) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C := ⟨⟩
  have hcl : ∀ x ∉ V, IsClosed ({x} : Set C) := by
    intro x hx
    let Z := irreducibleComponent x
    have hZ : Z ∈ irreducibleComponents C := irreducibleComponent_mem_irreducibleComponents x
    have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    let W := (⋃₀ (irreducibleComponents C \ {Z}))ᶜ
    have hW : IsOpen W := by
      dsimp [W]
      rw [Set.sUnion_eq_biUnion]
      exact (NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        fun S hS ↦ isClosed_of_mem_irreducibleComponents S hS.1).isOpen_compl
    have hclosure : closure W = Z :=
      closure_sUnion_irreducibleComponents_sdiff_singleton
        NoetherianSpace.finite_irreducibleComponents Z hZ
    have hWne : W.Nonempty := by
      by_contra he
      have he' : W = ∅ := Set.not_nonempty_iff_eq_empty.mp he
      have : Z = ∅ := by rw [← hclosure, he', closure_empty]
      exact hZ.1.nonempty.ne_empty this
    obtain ⟨v, hvW, hvV⟩ := hV.inter_open_nonempty W hW hWne
    have hvZ : v ∈ Z := hclosure ▸ subset_closure hvW
    have : IrreducibleSpace Z := Subtype.irreducibleSpace hZ.1
    have hdim : topologicalKrullDim Z ≤ 1 :=
      (topologicalKrullDim_subspace_le C Z).trans (IsCurve.krullDim_le_one f)
    have hclosed : IsClosed ({⟨x, mem_irreducibleComponent⟩} : Set Z) :=
      (V.isOpen.preimage continuous_subtype_val).isClosed_singleton_of_mem_compl hdim
        ⟨⟨v, hvZ⟩, hvV⟩ hx
    simpa using hZcl.isClosedMap_subtype_val _ hclosed
  have hfin : (V : Set C)ᶜ.Finite := by
    obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible V.isOpen.isClosed_compl
    rw [hS]
    refine hSf.sUnion fun t ht ↦ ?_
    obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hzV : z ∉ V := by
      have : z ∈ (V : Set C)ᶜ := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
      exact this
    have ht' : t = {z} := by rw [← hz.def, (hcl z hzV).closure_eq]
    rw [ht']
    exact Set.finite_singleton z
  refine ⟨hfin, hcl, ?_⟩
  intro x hx
  have : IsAlgClosed (C.residueField x) :=
    IsAlgClosed.of_ringEquiv k _
      (Iso.commRingCatIsoToRingEquiv (residueFieldIsoBase f x (hcl x hx))).symm
  infer_instance

end AlgebraicGeometry.IsCurve
