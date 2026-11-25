/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Restriction of locally quasi-finite morphisms to open subschemes

Source: Stacks Project, Morphisms of Schemes, Tags 01TD and 01TH (4), as invoked in
Tag 03JA (blueprint: lem-weil-pbc-lqf-restriction-to-opens).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- Restricting a locally quasi-finite morphism to open subschemes preserves local
quasi-finiteness in the Stacks sense, including the finite-type requirement.
Source: Stacks Project, Morphisms of Schemes, Tags 01TD and 01TH (4), as used in Tag 03JA
(blueprint: lem-weil-pbc-lqf-restriction-to-opens).

The open immersions are `U.ι` and `V.ι`. The canonical restriction `f.resLE V U e` satisfies
`f.resLE V U e ≫ V.ι = U.ι ≫ f` by `resLE_comp_ι`; uniqueness follows since `V.ι` is mono.

Proof:
1. By `locallyOfFiniteType_of_isLocallyQuasiFinite`, `f` is locally of finite type;
   Mathlib's restriction instance supplies the same property for `f.resLE V U e`.
2. For a point `x` of `U`, `quasiFiniteAtPoint_isolated_in_fiber` gives isolation of
   `U.ι x` in its fibre under `f`. Mathlib's `quasiFiniteAt_iff_isOpen_singleton_asFiber`
   turns this into the stalk-map predicate `f.QuasiFiniteAt (U.ι x)`.
3. Transfer this predicate across the two open immersions using
   `quasiFiniteAt_comp_iff`, `resLE_comp_ι`, and
   `quasiFiniteAt_comp_iff_of_isOpenImmersion`. The same fibre-isolation criterion,
   now for the restricted locally finite type morphism, gives isolation at `x`.
4. Choose an affine target neighbourhood of the image of `x` and an affine source
   neighbourhood of `x` inside its inverse image using the affine-open basis (01IT).
   Apply `isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber` to the restricted morphism
   and these opens. Its finite-type and quasi-finiteness witnesses give exactly
   `IsQuasiFiniteAtPoint (f.resLE V U e) x` by Definition 01TD.
5. Since `x` was arbitrary, Definition 01TD gives local quasi-finiteness. -/
theorem isLocallyQuasiFinite_resLE {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (hf : IsLocallyQuasiFinite f) (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    IsLocallyQuasiFinite (f.resLE V U e) := by
  have : AlgebraicGeometry.LocallyOfFiniteType f :=
    locallyOfFiniteType_of_isLocallyQuasiFinite f hf
  intro x
  have hx : f.QuasiFiniteAt (U.ι x) :=
    quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
      (quasiFiniteAtPoint_isolated_in_fiber f (U.ι x) (hf (U.ι x))).1
  have hx' : (f.resLE V U e).QuasiFiniteAt x := by
    rwa [← quasiFiniteAt_comp_iff (g := V.ι), resLE_comp_ι,
      quasiFiniteAt_comp_iff_of_isOpenImmersion]
  have hisolated : IsOpen ({(f.resLE V U e).asFiber x} :
      Set ((f.resLE V U e).fiber ((f.resLE V U e) x))) :=
    quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx'
  obtain ⟨V', hV', hyV', _⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := V) (x := (f.resLE V U e) x) (U := ⊤) (by trivial)
  obtain ⟨U', hU', hxU', hUV'⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := U) (x := x) (U := (f.resLE V U e) ⁻¹ᵁ V') hyV'
  exact ⟨U', hxU', hU', V', hV', hUV',
    isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber (f.resLE V U e) x hisolated
      U' V' hU' hV' hxU' hUV'⟩

end AlgebraicGeometry.Scheme.Hom
