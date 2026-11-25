/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.IsolatedFibrePointBaseChange
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Base change of separated and locally quasi-finite morphisms

Source: Stacks Project, Schemes, Lemma Tag 01KU (3), and Morphisms, Lemma Tag 01TM (2)
(blueprint: lem-weil-pbc-separated-lqf-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Separatedness and local quasi-finiteness are preserved by base change.
Source: Stacks Project, Tags 01KU and 01TM.

Proof:
1. The diagonal of the second projection is the base change of the diagonal of `f`.
   Closed immersions are stable under base change, giving the first implication
   (lem-weil-pbc-separated-base-change).
2. Local quasi-finiteness implies local finite type
   (lem-weil-pbc-lqf-locally-finite-type), which survives base change
   (lem-weil-pbc-lft-base-change).
3. For any point upstairs, quasi-finiteness at its image gives an isolated point of
   the fibre (lem-weil-pbc-quasi-finite-at-point-isolated). This isolation survives
   base change (lem-weil-pbc-isolated-fibre-point-base-change).
4. Choose affine neighbourhoods of the point and its image with the first mapping
   into the second (lem-weil-pbc-affine-opens-basis).
5. The isolated-fibre-point affine-pair criterion
   (lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs) gives a finite-type
   ring map quasi-finite at the corresponding prime. This is quasi-finiteness at
   the point (pqf-def-quasifinite). Since the point was arbitrary, the projection
   is locally quasi-finite.
(blueprint: lem-weil-pbc-separated-lqf-base-change)
-/
theorem separated_lqf_base_change {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    (IsSeparated f → IsSeparated (pullback.snd f g)) ∧
      (Scheme.Hom.IsLocallyQuasiFinite f →
        Scheme.Hom.IsLocallyQuasiFinite (pullback.snd f g)) := by
  constructor
  · intro hf
    have : IsSeparated f := hf
    infer_instance
  · intro hf
    have : LocallyOfFiniteType f := f.locallyOfFiniteType_of_isLocallyQuasiFinite hf
    intro x'
    have hisolated := isolated_fiber_point_base_change f g x'
      (f.quasiFiniteAtPoint_isolated_in_fiber (pullback.fst f g x')
        (hf (pullback.fst f g x'))).1
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show (pullback.snd f g) x' ∈ (⊤ : S'.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show x' ∈ (pullback.snd f g) ⁻¹ᵁ V from hxV)
    refine ⟨U, hxU, hU, V, hV, hUV, ?_⟩
    exact (pullback.snd f g).isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber
      x' hisolated U V hU hV hxU hUV

end AlgebraicGeometry
