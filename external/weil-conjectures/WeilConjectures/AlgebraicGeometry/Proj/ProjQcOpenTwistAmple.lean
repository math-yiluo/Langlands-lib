/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import WeilConjectures.AlgebraicGeometry.Proj.ProjTwistSectionBasicOpen
import WeilConjectures.AlgebraicGeometry.Proj.ProjCommonDegreeTwistInvertible
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import WeilConjectures.AlgebraicGeometry.NonvanishingLocusRestrict
import all WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN
import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option linter.privateModule false

/-!
# Sufficiently divisible twists on a quasi-compact Proj open

The statement records the common positive degree whose restricted Proj twists are
invertible and ample, together with the canonical tensor-power identification.

## References

* Stacks Project, Constructions, Tag 01MW and Properties, Tag 01Q2
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
private def tensorSection {X : Scheme.{u}} (M : X.Modules) (Q : X.Opens) :
    ∀ k : ℕ, (Fin k → Γ(M, Q)) → Γ(M.tensorPow k, Q)
  | 0, _ => Scheme.Modules.unitSectionsEquiv Q 1
  | k + 1, s => Scheme.Modules.tmulSection (s 0) (tensorSection M Q k (Fin.tail s))

end AlgebraicGeometry
