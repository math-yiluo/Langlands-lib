/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!

# The reduced closed subscheme on a set of points of an affine scheme

For a commutative ring `R` and a set `Z` of points of `Spec R`, the reduced closed subscheme with
support the closure of `Z` is `Spec (R ⧸ I(Z))`, `I(Z)` the vanishing ideal
(`AlgebraicGeometry.Scheme.reducedClosed`). It is reduced, its closed immersion into `Spec R` has
image the closure of `Z`, and the kernel of the map on global sections is `I(Z)`. These are the
reduced inverse images `G' ∪ V'`, `H'`, `B'` of blueprint `lemma-tangent-cones-on-cover`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (R : CommRingCat.{u}) (Z : Set (PrimeSpectrum R))

/-- The reduced closed subscheme `Spec (R ⧸ I(Z))` of `Spec R` with support the closure of `Z`. -/
noncomputable abbrev reducedClosed : Scheme.{u} :=
  Spec (.of (R ⧸ PrimeSpectrum.vanishingIdeal Z))

/-- The closed immersion `Spec (R ⧸ I(Z)) ⟶ Spec R`. -/
noncomputable abbrev reducedClosedι : reducedClosed R Z ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (PrimeSpectrum.vanishingIdeal Z)))

instance : IsClosedImmersion (reducedClosedι R Z) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

instance : IsReduced (reducedClosed R Z) := by
  have : _root_.IsReduced (R ⧸ PrimeSpectrum.vanishingIdeal Z) :=
    (Ideal.isRadical_iff_quotient_reduced _).1 (PrimeSpectrum.isRadical_vanishingIdeal Z)
  infer_instance

/-- The image of `Spec (R ⧸ I(Z)) ⟶ Spec R` is the closure of `Z`. -/
lemma range_reducedClosedι : Set.range (reducedClosedι R Z).base = closure Z := by
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact (range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).trans
    (by rw [Ideal.mk_ker])

end AlgebraicGeometry.Scheme
