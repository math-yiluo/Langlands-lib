/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
/-- The strict henselization structural fibre over the distinguished point contains no
point other than the closed point. This is the forward half of the singleton-fibre theorem.
Source: Stacks Project, Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-closed-fiber-forward)
Proof: choose an affine chart Spec R around p = s(closedPoint Ω) and factor s
through it. The initial chart restriction and the pointed etale residue-triple equivalence
identify the coordinate-ring colimit C defining the strict henselization with the triple
colimit, preserving the structural R-map on every coprojection. The residue embeddings
land in the relative separable closure of κ(p) inside Ω since etale residue extensions
are finite separable (Tag 04HX). Tags 04GW and 04GP give a local colimit whose maximal
ideal is pC. The prime corresponding to e(x) contracts to p, so it contains pC and equals
that maximal ideal. Therefore e(x) is the closed point of Spec C. An isomorphism preserves
closed singletons; its inverse sends this point to the unique closed point of Spec A.
Thus x = closedPoint A. The argument includes the field case. A zero ring A cannot have
the assumed isomorphism, since C has a nonzero field quotient. -/
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictLocalization s)
    (x : Spec (.of A))
    (h : (e.hom ≫ strictLocalizationToBase s) x =
      s (IsLocalRing.closedPoint Ω)) :
    x = IsLocalRing.closedPoint A := by
  classical
  obtain ⟨R, i, hi, hp, _⟩ := exists_affine_mem_range_and_range_subset
    (x := s (IsLocalRing.closedPoint Ω)) (U := ⊤) (by simp)
  let := hi
  have hrange : Set.range s ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint Ω)] using hp
  let xR := IsOpenImmersion.lift i s hrange
  have hfac : xR ≫ i = s := IsOpenImmersion.lift_fac i s hrange
  have hchart := strictHenselization_chart_maximalIdeal R i xR
  rw [hfac] at hchart
  obtain ⟨hlocal, ρ, hρ, hm⟩ := hchart
  let := hlocal
  have hcontract : Spec.map ρ (e.hom x) = xR (IsLocalRing.closedPoint Ω) := by
    apply i.isOpenEmbedding.injective
    have hh : (Spec.map ρ ≫ i) (e.hom x) = (xR ≫ i) (IsLocalRing.closedPoint Ω) := by
      rw [hρ, hfac]
      exact h
    simpa only [Scheme.Hom.comp_apply] using hh
  have hprime : (e.hom x).asIdeal =
      IsLocalRing.maximalIdeal (strictHenselization s) := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (e.hom x).isPrime.ne_top
    · rw [hm, Ideal.map_le_iff_le_comap]
      exact le_of_eq (congrArg PrimeSpectrum.asIdeal hcontract).symm
  have hx : e.hom x = IsLocalRing.closedPoint (strictHenselization s) :=
    PrimeSpectrum.ext hprime
  have hspecial := (IsLocalRing.specializes_closedPoint
    (e.inv (IsLocalRing.closedPoint (strictHenselization s))))
  have hback : IsLocalRing.closedPoint (strictHenselization s) ⤳
      e.hom (IsLocalRing.closedPoint A) := by
    have ht := hspecial.map e.hom.continuous
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id] at ht
    exact ht
  have he : e.hom (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (strictHenselization s) :=
    ((IsLocalRing.specializes_closedPoint _).antisymm hback).eq
  apply e.hom.isOpenEmbedding.injective
  exact hx.trans he.symm
end AlgebraicGeometry.Scheme
