/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.FiniteFieldClosedComponentDescent
import WeilConjectures.AlgebraicGeometry.ClosedComponentDescentTopology

/-!
# Finite descent of irreducible components from a separable closure

Source: Stacks Project, Tag 04KZ, parts (1) and (2), and Tag 054R.
(blueprint: lem-sbc-components-finite-separable-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- When the base change to a separable closure has finitely many components, one finite
intermediate field makes the inverse image of each component a single component.

Source: Stacks Project, Tag 04KZ, parts (1) and (2), and the proof of Tag 054R.
Proof: write Ω for the separable closure of k. For each component of X_Ω choose an affine
open of X meeting it. The corresponding minimal prime in its finite type Ω-algebra has
finitely many generators. Each generator uses finitely many coefficients of Ω, so all of
these generators for the finitely many components lie over a finite intermediate field L.
The subgroup Gal(Ω/L) fixes every component: it fixes its defining ideal on the chosen open,
and therefore its closure. Galois descent of invariant closed subsets gives a closed subset
of X_L for each component of X_Ω. Each descended subset is a component: faithful flatness
reflects proper inclusions, and lifting generalizations would otherwise contradict the
maximality of the component upstairs. Every component of X_L is the image of a component
upstairs, since the projection is integral, flat and surjective. Because all components
upstairs are invariant, its full inverse image is that one component. The tower pullback
isomorphism identifies X_Ω with the iterated pullback used in the conclusion. For an empty
scheme choose the bottom intermediate field; the component assertion is vacuous.

(blueprint: lem-sbc-components-finite-separable-descent) -/
theorem exists_finite_intermediateField_component_preimages {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hfinite : (irreducibleComponents
      ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))))).Finite) :
    ∃ L : IntermediateField k (SeparableClosure k),
      Module.Finite k L ∧
      ∀ A ∈ irreducibleComponents
        ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
        (pullback.fst
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
          (Spec.map (CommRingCat.ofHom L.subtype))) ⁻¹' A ∈
            irreducibleComponents
              ↥(pullback
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
                (Spec.map (CommRingCat.ofHom L.subtype))) := by
  obtain ⟨L, hL, hsurj, hfin, hdesc⟩ :=
    exists_finite_intermediateField_closed_component_descent f hfinite
  refine ⟨L, hL, ?_⟩
  exact component_preimages_of_closed_descent _ (Scheme.Hom.continuous _) hsurj hfin hdesc

end AlgebraicGeometry
