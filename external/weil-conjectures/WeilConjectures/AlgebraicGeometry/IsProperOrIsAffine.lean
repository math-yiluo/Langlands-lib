/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Curve.Compactification

@[expose] public section

/-!
# A smooth separated connected curve is proper or affine

Source: Stacks Project, Varieties, Lemma 33.43.11 (Tag 0A28), and the blueprint
compactification route for `proposition-cohomology-smooth-affine-curve` (blueprint:
lem-sc-proper-or-affine).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/- A smooth separated connected curve over an algebraically closed field is proper or affine.
Source: Stacks Project, Varieties, Lemma 0A28 (Tag 0A28)
(blueprint: lem-sc-proper-or-affine).

Proof, step 1: by lemma-proper-smooth-model--1, embed the curve as an open subscheme of a
proper smooth connected curve, with boundary a finite set of closed points. The algebraically
closed field hypothesis is part of def-sc-curves.
Step 2: if the boundary is empty, the open immersion is surjective and hence an isomorphism;
properness transfers from the compactification to the original curve. If the boundary is
nonempty, proposition-p-torsion-smooth-proper-curve--3 says the open curve is affine. These cases
exhaust all possibilities. -/
set_option linter.style.haveILetI false in
/-- (blueprint: lem-sc-proper-or-affine) -/
theorem IsConnectedCurve.isProper_or_isAffine
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] :
    IsProper f ∨ IsAffine C := by
  obtain ⟨c, hc, hs, hfin, hclosed⟩ :=
    IsConnectedCurve.exists_smooth_properCompactification f
  by_cases hS : (Set.range c.i.base)ᶜ = ∅
  · left
    have hrange : Set.range c.i.base = Set.univ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        by_contra hxn
        have hxc : x ∈ (Set.range c.i.base)ᶜ := by
          simpa [Set.mem_compl_iff] using hxn
        rw [hS] at hxc
        exact hxc
    have hsurj : Function.Surjective c.i.base := Set.range_eq_univ.mp hrange
    letI : Surjective c.i := ⟨hsurj⟩
    haveI : IsIso c.i := (isIso_iff_isOpenImmersion_and_surjective c.i).mpr
      ⟨inferInstance, inferInstance⟩
    rw [c.comm]
    infer_instance
  · right
    let V : c.Z.Opens := c.i.opensRange
    have hV : V ≠ ⊤ := by
      intro h
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hS
      have hx' : x ∈ (V : Set c.Z) := by
        rw [h]
        trivial
      exact hx hx' 
    have hAff : IsAffine V :=
      IsConnectedCurve.isAffine_of_ne_top c.g V hV
    exact IsAffine.of_isIso c.i.isoOpensRange.hom

end AlgebraicGeometry
