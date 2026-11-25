/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # The generic stalk of a regular effective Cartier divisor

## References

* Stacks Project, Tag 0EYG (the height-one divisor calculation), and Tag 00PD (the one-dimensional
  regular local ring criterion)
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- At the generic point of an integral effective Cartier divisor, a regular ambient
stalk is a discrete valuation ring. -/
theorem regular_cartier_generic_stalk_dvr
    {X D : Scheme.{u}} (j : D ⟶ X) (hD : IsIntegral D)
    (hj : IsEffectiveCartierCenter j) (η : D) (hη : IsGenericPoint η Set.univ)
    (hreg : IsRegularLocalRing (X.presheaf.stalk (j η))) :
    ∃ hdom : IsDomain (X.presheaf.stalk (j η)),
      letI := hdom
      IsDiscreteValuationRing (X.presheaf.stalk (j η)) := by
  let := hD
  let := hreg
  let := hj.isClosedImmersion
  have hηeq : η = genericPoint D := ((genericPoint_spec D).eq hη).symm
  have hfield : IsField (D.presheaf.stalk η) := by
    rw [hηeq]
    exact Field.toIsField D.functionField
  let := hfield.toField
  have hdom : IsDomain (X.presheaf.stalk (j η)) := inferInstance
  refine ⟨hdom, ?_⟩
  let := hdom
  have hker := IsLocalRing.ker_eq_maximalIdeal (j.stalkMap η).hom
    (j.stalkMap_surjective η)
  obtain ⟨U, hηU, hU⟩ :=
    (isEffectiveCartierCenter_iff_isInvertible_ker.mp hj) (j η)
  let := X.presheaf.algebra_section_stalk (⟨j η, hηU⟩ : U.1)
  let := U.2.isLocalization_stalk ⟨j η, hηU⟩
  have hflat : (X.presheaf.germ U.1 (j η) hηU).hom.Flat := by
    change Module.Flat Γ(X, U.1) (X.presheaf.stalk (j η))
    exact IsLocalization.flat (X.presheaf.stalk (j η))
      (U.2.primeIdealOf ⟨j η, hηU⟩).asIdeal.primeCompl
  have hprincipal := hU.map_of_flat hflat
  rw [← j.ker_stalkMap U η hηU, hker] at hprincipal
  obtain ⟨t, ht, hspan⟩ := hprincipal
  exact IsDiscreteValuationRing.of_maximalIdeal_eq_span_singleton
    (nonZeroDivisors.ne_zero ht) hspan

end AlgebraicGeometry.Scheme
