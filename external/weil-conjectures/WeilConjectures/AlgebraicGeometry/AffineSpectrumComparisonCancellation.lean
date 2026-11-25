/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates
import WeilConjectures.AlgebraicGeometry.AffineSpectrumUnitNormalization
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare

/-! # AffineSpectrumComparisonCancellation

Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-affine-spectrum-comparison-cancellation).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The inverse unit component of the constructed spectrum equivalence, with its
pullback endpoints stated explicitly. No new choice of data is made.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-affine-spectrum-comparison-cancellation). -/
noncomputable def affineSpectrumUnitInv (X : Scheme.{u}) [IsAffine X]
    (K : schemeDerivedCategory X) :
    (derivedPullback X.toSpecΓ).obj ((derivedPullback X.isoSpec.inv).obj K) ⟶ K :=
  (affineSpectrumInversePullbackEquivalence X).unitIso.inv.app K

/-- Forward and inverse spectrum pullback comparisons cancel the equivalence unit.

Proof: expand the two comparisons into c, scheme naturality, and inverse c.
The unit of Equivalence.mk is adjointified: first apply composition
associativity and the unit laws to the isoSpec hom-inverse identities to prove
that the original composition unit and counit satisfy the triangle identity.
Since adjointification retains the counit, uniqueness of an adjunction unit
with that counit identifies the constructed unit with the original one.
Now expand that unit's inverse in c and the identity comparison. Use the
associativity law for c on gprime, isoSpec.hom, and isoSpec.inv. The two scheme
naturality equalities identify the composite maps. The hom-inverse equation
for isoSpec and the right and left unit laws for c cancel the inverse spectrum
factors. The remaining comparison is pullback of the inverse unit at K, as on
the right. This calculation uses no adjunction or base-change mate and works
for identities, empty schemes and zero objects.
Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-affine-spectrum-comparison-cancellation). -/
theorem affineSpectrum_comparison_cancellation
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) :
    (affineSpectrumForwardPullbackIso g').hom.app ((derivedPullback X.isoSpec.inv).obj K) ≫
      (derivedPullback X'.toSpecΓ).map
        ((affineSpectrumDerivedPullbackIso g').hom.app K) ≫
      affineSpectrumUnitInv X' ((derivedPullback g').obj K) =
    (derivedPullback g').map
      (affineSpectrumUnitInv X K) := by
  simp only [affineSpectrumUnitInv, affineSpectrum_unit_normalization]
  exact affineSpectrum_composition_unit_square g' K

end AlgebraicGeometry
