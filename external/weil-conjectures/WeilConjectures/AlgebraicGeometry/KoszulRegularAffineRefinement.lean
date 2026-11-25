/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.RingTheory.KoszulRegularFlatBaseChange
import Mathlib.RingTheory.Flat.Localization

/-! # Refining regular affine charts

Source: Stacks Project, Tags 062H and 01I1.
(blueprint: new-s3-koszul-regular-affine-refinement). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A regular affine chart can be refined inside another affine neighborhood.

Source: Stacks Project, Tag 062H, flat base change of Koszul regularity;
Tag 01I1, distinguished opens form a basis.
(blueprint: new-s3-koszul-regular-affine-refinement).

Proof: Choose a distinguished open D(s) of U containing i(z) and contained in
U'. The ring of its sections is the localization of Gamma(Y,U) at s. Restrict
the given generators along this localization. Their ideal is the restricted
immersion ideal, because quasi-coherent ideals localize on distinguished opens.
Localization is flat, so the restricted sequence is Koszul-regular by Tag 062H.
D(s) is affine and contains the chosen point. No affine-intersection hypothesis
is used. For the empty sequence the ideal remains zero. Empty neighborhoods
cannot satisfy the point-membership hypotheses; the zero ring causes no extra
case. -/
theorem koszulRegularImmersion_affine_refinement
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U U' : Y.affineOpens) (z : Z) (hz : i z ∈ U.1) (hz' : i z ∈ U'.1)
    (hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
      Ideal.span (Set.range f) = i.ker.ideal U ∧
        RingTheory.Sequence.IsKoszulRegular f) :
    ∃ U₀ : Y.affineOpens, i z ∈ U₀.1 ∧ U₀.1 ≤ U.1 ∧ U₀.1 ≤ U'.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U₀.1)),
        Ideal.span (Set.range f) = i.ker.ideal U₀ ∧
          RingTheory.Sequence.IsKoszulRegular f := by
  obtain ⟨m, f, hf, hreg⟩ := hU
  obtain ⟨s, hs, hzs⟩ := U.2.exists_basicOpen_le ⟨i z, hz'⟩ hz
  let U₀ : Y.affineOpens := Y.affineBasicOpen s
  let A := (Γ(Y, U.1) : Type u)
  let S := (Γ(Y, U₀.1) : Type u)
  let : Algebra A S := (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom.toAlgebra
  have : IsLocalization.Away s S := U.2.isLocalization_basicOpen s
  have : Module.Flat A S := IsLocalization.flat S (Submonoid.powers s)
  refine ⟨U₀, hzs, Y.basicOpen_le s, hs, m, algebraMap A S ∘ f, ?_,
    RingTheory.Sequence.isKoszulRegular_of_flat A S m f hreg⟩
  rw [← i.ker.map_ideal (U := U₀) (V := U) (Y.basicOpen_le s), ← hf,
    Ideal.map_span]
  congr 1
  exact Set.range_comp _ _

end AlgebraicGeometry
