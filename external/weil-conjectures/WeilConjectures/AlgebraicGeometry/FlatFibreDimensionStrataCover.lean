/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.RestrictedFibreLocallyNoetherian

/-! # Dense fibre opens contain component generic points

Source: Stacks Project, Tag 054U.
(blueprint: lem-sbc-flat-fibre-dimension-strata-cover)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem generic_points_subset_dense_open (Y : Scheme.{u})
    [IsLocallyNoetherian Y] (W : Set Y) (hopen : IsOpen W) (hdense : Dense W) :
    genericPoints Y ⊆ W := by
  intro z hz
  obtain ⟨A, hA, hzA, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := z) (by simp)
  have : IsNoetherianRing Γ(Y, A) :=
    IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  let instA : TopologicalSpace.NoetherianSpace A := noetherianSpace_of_isAffineOpen A hA
  have hcomp := preimage_mem_irreducibleComponents hz A.isOpenEmbedding'
    (show (closure {z} ∩ Set.range (fun a : A ↦ (a : Y))).Nonempty from
      ⟨z, subset_closure (by simp), ⟨⟨z, hzA⟩, rfl⟩⟩)
  obtain ⟨O, hO, hOne, hOsub⟩ :=
    @TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      A _ instA _ hcomp
  obtain ⟨y, hyO, hyW⟩ :=
    (hdense.preimage A.isOpenEmbedding'.isOpenMap).inter_open_nonempty O hO hOne
  have hsp : z ⤳ (y : Y) := specializes_iff_mem_closure.mpr (hOsub hyO)
  exact hsp.mem_open hopen hyW

/-- Dense fibre opens contain component generic points.

Source: Stacks Project, Tags 054T and 054U.
Proof: For t in U, the fibre is isomorphic to a fibre of the restricted locally finitely presented
morphism. It is locally of finite type over the residue field and hence locally noetherian. Fix a
component generic point z and choose a noetherian affine open neighbourhood A of z. The
intersection of its component with A is an irreducible component of A and has generic point z.
There are finitely many components of A. Remove all the other components; the resulting open O
contains z and is contained in its component, and is nonempty. The dense open W intersects O in a
point y. Since y belongs to the closure of z, z generalizes y; openness of W forces z to lie in W.
This proves the inclusion for every component generic point. Empty fibres have no component
generic points.
(blueprint: lem-sbc-flat-fibre-dimension-strata-cover) -/
theorem generic_points_mem_dense_open_fibre_of_flat_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (t : T) (ht : t ∈ U) (W : Set (f.fiber t))
    (hopen : IsOpen W) (hdense : Dense W) :
    genericPoints (f.fiber t) ⊆ W := by
  have := isLocallyNoetherian_fibre_of_finite_presentation_restrict f U t ht
  exact generic_points_subset_dense_open (f.fiber t) W hopen hdense

end AlgebraicGeometry
