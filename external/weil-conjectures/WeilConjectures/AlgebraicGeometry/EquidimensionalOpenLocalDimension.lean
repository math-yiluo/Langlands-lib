/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic

/-! # Local dimension of an equidimensional open in a locally algebraic scheme

Source: Stacks Project, Tag 0A21 (3), (5).
(blueprint: lem-sbc-equidimensional-open-local-dimension)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Pure dimension of an open in a locally algebraic scheme gives its local dimension.

Source: Stacks Project, Tag 0A21 (3), (5).
Proof: In the sober open subspace O, dimension is the supremum of the dimensions
of closures of points. Each such closure embeds in an irreducible component,
so hdim bounds dim O, and therefore every open neighbourhood, by n.
For the reverse bound fix a component C through x and construct its closed
subscheme using the vanishing ideal on O. Its underlying space is homeomorphic
to C, it is irreducible, and its map to Spec k is locally of finite type.
For each open neighbourhood U of x in O, the inverse image of U in this closed
subscheme is nonempty. The existing dimension_locally_algebraic theorem
(Tag 0A21 (3)) gives its dimension as dim C = n. Its embedding into U gives
n <= dim U. Thus all neighbourhoods have dimension n; take their infimum and
transport local dimension from O to Y by IsOpen.topologicalKrullDimAt_eq.
Empty O has no points, so the statement is vacuous. The vanishing-ideal
subscheme is an actual construction; no object is chosen from an unproved
existence statement.
(blueprint: lem-sbc-equidimensional-open-local-dimension) -/
theorem topologicalKrullDimAt_eq_of_equidimensional_open
    {k : Type u} [Field k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType g] (O : Y.Opens) (n : ℕ)
    (hdim : ∀ C ∈ irreducibleComponents ↥O, topologicalKrullDim C = (n : WithBot ℕ∞))
    (x : Y) (hx : x ∈ O) : topologicalKrullDimAt x = (n : WithBot ℕ∞) := by
  let z : O := ⟨x, hx⟩
  have hupper : topologicalKrullDim O ≤ (n : WithBot ℕ∞) := by
    let : QuasiSober O := O.isOpenEmbedding'.quasiSober
    let := specializationOrder O
    rw [topologicalKrullDim_eq_krullDim_specializationOrder, Order.krullDim_eq_iSup_height]
    refine iSup_le fun y ↦ ?_
    let C := irreducibleComponent y
    have hC := irreducibleComponent_mem_irreducibleComponents y
    have hsub : closure ({y} : Set O) ⊆ C :=
      closure_minimal (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
        (isClosed_of_mem_irreducibleComponents C hC)
    rw [← topologicalKrullDim_closure_singleton]
    exact ((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans
      (hdim C hC).le
  have hlocal : topologicalKrullDimAt z = (n : WithBot ℕ∞) := by
    apply topologicalKrullDimAt_eq_of_forall
    intro U hzU
    have hUle : topologicalKrullDim U ≤ topologicalKrullDim O :=
      Topology.IsInducing.subtypeVal.topologicalKrullDim_le
    apply le_antisymm (hUle.trans hupper)
    let C := irreducibleComponent z
    have hC := irreducibleComponent_mem_irreducibleComponents z
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨C, isClosed_of_mem_irreducibleComponents C hC⟩ : TopologicalSpace.Closeds O.toScheme)
    let i : I.subscheme ⟶ O.toScheme := I.subschemeι
    have hr : Set.range i = C := by
      exact Scheme.IdealSheafData.range_subschemeι I |>.trans
        (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
    let e : I.subscheme ≃ₜ C := i.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hr)
    have : IrreducibleSpace C := Subtype.irreducibleSpace hC.1
    have : IrreducibleSpace I.subscheme := e.irreducibleSpace_iff.mpr inferInstance
    let : I.subscheme.Over (Spec (.of k)) := ⟨i ≫ O.ι ≫ g⟩
    have : LocallyOfFiniteType (I.subscheme ↘ Spec (.of k)) := by
      change LocallyOfFiniteType (i ≫ O.ι ≫ g)
      infer_instance
    let V : I.subscheme.Opens := i ⁻¹ᵁ U
    have hV : (V : Set I.subscheme).Nonempty := by
      obtain ⟨w, hw⟩ := hr.ge (mem_irreducibleComponent (x := z))
      exact ⟨w, by change i w ∈ U; rwa [hw]⟩
    have hdimV := (dimension_locally_algebraic (k := k) I.subscheme).1 V hV
    have hdimI : topologicalKrullDim I.subscheme = (n : WithBot ℕ∞) :=
      (e.isHomeomorph.topologicalKrullDim_eq e).trans (hdim C hC)
    rw [← hdimI, ← hdimV]
    exact (i.isClosedEmbedding.isEmbedding.restrictPreimage U.1).isInducing.topologicalKrullDim_le
  exact (O.isOpen.topologicalKrullDimAt_eq hx).symm.trans hlocal

end AlgebraicGeometry
