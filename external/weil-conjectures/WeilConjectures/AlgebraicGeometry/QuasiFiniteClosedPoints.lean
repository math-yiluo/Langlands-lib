/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!

# Preimages of closed points under quasi-finite morphisms

For a locally quasi-finite morphism of schemes `f : X ⟶ Y`, a point of `X` lying over a closed
point of `Y` is closed (`AlgebraicGeometry.Scheme.Hom.isClosed_singleton_of_isClosed_singleton`),
since the fibres of `f` are discrete. If `f` is moreover quasi-compact, the preimage of a finite
set of closed points is a finite set of closed points
(`AlgebraicGeometry.Scheme.Hom.exists_finset_preimage_of_isClosed_singleton`).

This is used in the finite-support step of Gabber's Künneth formula (blueprint
`proposition-external-kunneth-formula-nearby-cycles`): the support of the cone of the Künneth map is
contained in the preimage, under a quasi-finite coordinate map, of a finite set of closed points.

-/

@[expose] public section

namespace AlgebraicGeometry

variable {X Y : Scheme} (f : X ⟶ Y)

/-- A point lying over a closed point under a locally quasi-finite morphism is closed. -/
lemma Scheme.Hom.isClosed_singleton_of_isClosed_singleton [LocallyQuasiFinite f] {x : X}
    (hx : IsClosed {f x}) : IsClosed {x} := by
  have hF : IsClosed (f ⁻¹' {f x}) := hx.preimage f.continuous
  refine closure_subset_iff_isClosed.1 fun z hz ↦ ?_
  have hxz : x ⤳ z := specializes_iff_mem_closure.2 hz
  have hzF : z ∈ f ⁻¹' {f x} :=
    closure_minimal (s := ({x} : Set X)) (t := f ⁻¹' {f x})
      (Set.singleton_subset_iff.2 (Set.mem_preimage.2 (Set.mem_singleton _))) hF hz
  exact ((f.isDiscrete_preimage_singleton (f x)).eq_of_specializes hxz rfl hzF).symm

/-- The preimage of a finite set of closed points under a quasi-compact, locally quasi-finite
morphism is a finite set of closed points. -/
lemma Scheme.Hom.exists_finset_preimage_of_isClosed_singleton [LocallyQuasiFinite f]
    [QuasiCompact f] (S : Finset Y) (hS : ∀ y ∈ S, IsClosed {y}) :
    ∃ T : Finset X, (T : Set X) = f ⁻¹' S ∧ ∀ x ∈ T, IsClosed {x} := by
  refine ⟨(f.finite_preimage S.finite_toSet).toFinset, by simp, fun x hx ↦ ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe] at hx
  exact f.isClosed_singleton_of_isClosed_singleton (hS _ hx)

end AlgebraicGeometry
