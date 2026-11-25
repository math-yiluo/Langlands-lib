/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.Blowup.Affine.Principalization

/-!
# Regularity and coordinate intersections on a permissible blowup chart

The auxiliary definitions are the displayed presentation and its coordinate equations.
Reduced unions are expressed by radical ideals. Strict transforms use the existing
scheme-theoretic closure construction, rather than topological closures.

## References

* Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VIII, Lemma 4.2.9, printed p. 121, and Remark
  4.2.2(i), printed p. 118
* ILO VIII, Lemma 4.2.9, p. 121
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PermissibleCoordinateChart

variable {R : Type u} [CommRing R] {d : ℕ}

/-- The exceptional hyperplane together with the strict transforms indexed by `I`. -/
def labels (I : Finset (Fin d)) (j : Fin d) : Finset (Option (Fin d)) :=
  insert none ((I.erase j).image some)

/-- The closed immersion of a coordinate hyperplane in the base. -/
def hyperplane (a : R) : Spec (.of (R ⧸ (Ideal.span {a} : Ideal R))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a} : Ideal R)))

end AlgebraicGeometry.PermissibleCoordinateChart
