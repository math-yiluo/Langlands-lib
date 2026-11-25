/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberForward
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberBackward

/-!
# The fibre of a strict henselization over its distinguished point

Source: Stacks Project, Tags 04HX, 04GW and 04GP, strict henselization construction.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The only point of the strict henselization over the underlying geometric point is
its closed point, in any local affine presentation.
Source: Stacks Project, Tags 04HX, 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-closed-fiber)

Proof: choose an affine neighbourhood Spec R of the image p of s. The pointed etale
coordinate-ring colimit is the strict henselization of R_p (Tag 04HX): localizing each
neighbourhood at its selected prime does not change the colimit, since every element
outside that prime becomes invertible on a smaller pointed open neighbourhood. Its
maximal ideal is p times the colimit ring, and its quotient is the separable algebraic
closure of the residue field of p inside Ω. In particular that quotient is a field.
Thus the fibre over p has exactly one prime, the maximal ideal: primes over p contain
p times the colimit ring, and conversely that maximal ideal contracts to p. Under the
isomorphism e this point is the closed point of A, since an isomorphism of spectra
preserves closed points and a local ring has a unique closed point. Both implications
of the displayed equivalence follow. This argument also covers a field A, whose
closed point is its zero ideal. -/
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictLocalization s)
    (x : Spec (.of A)) :
    (e.hom ≫ strictLocalizationToBase s) x = s (IsLocalRing.closedPoint Ω) ↔
      x = IsLocalRing.closedPoint A := by
  constructor
  · exact strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq s e x
  · intro hx
    subst x
    exact strictHenselizationStructuralMap_closedPoint_eq s e

end AlgebraicGeometry.Scheme
