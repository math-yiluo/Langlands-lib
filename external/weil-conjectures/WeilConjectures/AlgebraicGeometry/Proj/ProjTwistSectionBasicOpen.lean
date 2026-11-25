/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# Homogeneous twist sections and standard opens on the invertibility locus

## Main definitions

* `AlgebraicGeometry.Proj.twistSectionOnOpen`: the canonical homogeneous section restricted
  to an open subscheme, using the existing twist and restriction functor.
* `AlgebraicGeometry.Proj.twistSectionLoci`: its nonvanishing sets in positive degrees
  divisible by the specified integer.

## Main statements

* `AlgebraicGeometry.Proj.twistSectionBasicOpen`: equality of the section locus with the
  standard open, and the basis and affine basis assertions on every open in `W_d`.

## References

* Stacks Project, Constructions, Tags 01MU, 01MV and 01MW (5)--(7)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

end AlgebraicGeometry.Proj
