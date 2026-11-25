/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite

/-!
# Comparison with Mathlib's quasi-finite morphisms

The quasi-finiteness predicates of Stacks Tag 01TD include local finite type, which Mathlib's
`LocallyQuasiFinite` and `Scheme.Hom.QuasiFiniteAt` do not. We show that they agree with
Mathlib's notions once the finite-type conditions are added.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPoint_iff_quasiFiniteAt`: for `f` locally of
  finite type, `IsQuasiFiniteAtPoint f x ↔ f.QuasiFiniteAt x`.
- `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_iff`:
  `IsLocallyQuasiFinite f ↔ LocallyQuasiFinite f ∧ LocallyOfFiniteType f`.
- `AlgebraicGeometry.Scheme.Hom.isQuasiFinite_iff`:
  `IsQuasiFinite f ↔ LocallyQuasiFinite f ∧ LocallyOfFiniteType f ∧ QuasiCompact f`.

Source: Stacks Project, Morphisms of Schemes, Tags 01TD, 01TF and 01TJ
(blueprint: pqf-def-quasifinite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For a morphism locally of finite type, quasi-finiteness at a point in the sense of Stacks
Tag 01TD is Mathlib's `Scheme.Hom.QuasiFiniteAt`: both say that the point is isolated in its
fibre (Stacks, Tag 01TF). -/
theorem isQuasiFiniteAtPoint_iff_quasiFiniteAt [LocallyOfFiniteType f] (x : X) :
    IsQuasiFiniteAtPoint f x ↔ f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  refine ⟨fun h ↦ (quasiFiniteAtPoint_isolated_in_fiber f x h).1, fun h ↦ ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
  exact ⟨U, hxU, hU, V, hV, hUV,
    f.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber x h U V hU hV hxU hUV⟩

/-- Locally quasi-finite in the sense of Stacks Tag 01TD is Mathlib's `LocallyQuasiFinite`
together with `LocallyOfFiniteType`. -/
theorem isLocallyQuasiFinite_iff :
    IsLocallyQuasiFinite f ↔ LocallyQuasiFinite f ∧ LocallyOfFiniteType f := by
  constructor
  · intro hf
    have := locallyOfFiniteType_of_isLocallyQuasiFinite f hf
    refine ⟨locallyQuasiFinite_iff_isDiscrete_preimage_singleton.2 fun s ↦ ?_, this⟩
    rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
    rintro ⟨y, hy⟩
    obtain rfl : f y = s := hy
    exact (quasiFiniteAtPoint_isolated_in_fiber f y (hf y)).2
  · rintro ⟨_, _⟩ x
    exact (isQuasiFiniteAtPoint_iff_quasiFiniteAt f x).2 (f.quasiFiniteAt x)

/-- Quasi-finite in the sense of Stacks Tag 01TD is Mathlib's `LocallyQuasiFinite` together with
`LocallyOfFiniteType` and `QuasiCompact` (Stacks, Tag 01TJ). -/
theorem isQuasiFinite_iff :
    IsQuasiFinite f ↔ LocallyQuasiFinite f ∧ LocallyOfFiniteType f ∧ QuasiCompact f := by
  rw [isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact, isLocallyQuasiFinite_iff,
    and_assoc]

end AlgebraicGeometry.Scheme.Hom
