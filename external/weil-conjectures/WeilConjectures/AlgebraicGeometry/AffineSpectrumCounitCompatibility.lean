/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumComparisonCancellation
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCoordinateCounit

/-! # AffineSpectrumCounitCompatibility

Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-affine-spectrum-counit-compatibility).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory
namespace AlgebraicGeometry


variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The direct-image comparison preserves the pinned adjunction counit.

Proof: expand affineSpectrumDerivedDirectImageIso as the inverse left unitor,
whiskered unit of the inverse spectrum equivalence, associator, and conjugate d.
Apply conjugateEquiv_counit to d for the composed pinned adjunctions. Expand the
composite counits. Naturality of the equivalence unit moves it across the counit
of f. The equivalence triangle identities cancel that unit against its counit.
The forward pullback comparison is the inverse-spectrum pullback comparison
transported across the two spectrum equivalences: expand both using c, and use
its associativity and unit laws and isoSpec naturality. This gives the displayed
counit identity. There is only one morphism f and one object K, with no square.
Empty schemes and zero objects are included by the categorical identities.
Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-affine-spectrum-counit-compatibility). -/
theorem affineSpectrum_counit_compatibility
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (K : schemeDerivedCategory X) :
  (derivedPullback f).map ((affineSpectrumDerivedDirectImageIso f).hom.app K) ≫
      (affineSpectrumForwardPullbackIso f).hom.app
        ((schemeDerivedDirectImage (Spec.map f.appTop)).obj
          ((derivedPullback X.isoSpec.inv).obj K)) ≫
      (derivedPullback X.toSpecΓ).map
        ((canonicalSchemeDerivedAdjunction (Spec.map f.appTop)).counit.app
          ((derivedPullback X.isoSpec.inv).obj K)) ≫
      affineSpectrumUnitInv X K =
    (canonicalSchemeDerivedAdjunction f).counit.app K := by
  exact coordinate_counit_compatibility
    (derivedPullback f) (schemeDerivedDirectImage f)
    (derivedPullback (Spec.map f.appTop)) (schemeDerivedDirectImage (Spec.map f.appTop))
    (derivedPullback X.isoSpec.inv) (derivedPullback X.toSpecΓ)
    (derivedPullback S.isoSpec.inv) (derivedPullback S.toSpecΓ)
    (canonicalSchemeDerivedAdjunction f)
    (canonicalSchemeDerivedAdjunction (Spec.map f.appTop))
    (affineSpectrumInversePullbackEquivalence X).toAdjunction
    (affineSpectrumInversePullbackEquivalence S).toAdjunction
    (affineSpectrumInversePullbackEquivalence X).unitIso
    (affineSpectrumInversePullbackEquivalence S).unitIso
    rfl rfl (affineSpectrumDerivedPullbackIso f) (affineSpectrumForwardPullbackIso f)
    (affineSpectrumUnitInv X) (affineSpectrumUnitInv S)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
    (affineSpectrum_comparison_cancellation f)
    (affineSpectrumDerivedDirectImageIso f) (by
      intro L
      dsimp only [affineSpectrumDerivedDirectImageIso]
      set_option backward.isDefEq.respectTransparency false in
      simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
        Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Category.id_comp]
      delta canonicalSchemeDerivedAdjunction
      rfl) K

end AlgebraicGeometry
