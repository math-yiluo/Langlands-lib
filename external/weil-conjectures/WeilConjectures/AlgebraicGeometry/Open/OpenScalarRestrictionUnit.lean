/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.AlgebraicGeometry.OpenScalarTensor.OpenScalarTensorData
import all WeilConjectures.SmoothPurity.Compact.CompactSupportOpenScalarRestriction
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Scalar restriction preserves the open adjunction unit

## References

* Stacks Project, Tags 03DI, 03CY and 015F
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem ordinaryUnit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) :
    ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight
        (openSquarePullbackModel A j).symm).unit.app
        ((proEtaleCoefficientRestrictScalars X φ).obj M) ≫
      (proEtaleConstantRingPullback A j).map ((sfOpenRestriction j φ).hom.app M) ≫
      (WeilConjectures.compactSupportScalarPullback j φ).app
        ((sfIntrinsicExtensionByZero j B).obj M) =
    (proEtaleCoefficientRestrictScalars X φ).map
      (((sfIntrinsicOpenAdjunction B j).ofNatIsoRight
        (openSquarePullbackModel B j).symm).unit.app M) := by
  have hu (R : Type u) [CommRing R] [Finite R]
      (N : proEtaleRingModules X (proEtaleConstantRing X R)) :
      ((sfIntrinsicOpenAdjunction R j).ofNatIsoRight
          (openSquarePullbackModel R j).symm).unit.app N ≫
        (WeilConjectures.compactSupportOpenRestrictionModel R j).hom.app
          ((sfIntrinsicExtensionByZero j R).obj N) =
      (sfIntrinsicExtensionByZeroAdjunction j R).unit.app N := by
    simp only [Adjunction.ofNatIsoRight_unit, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, WeilConjectures.compactSupportOpenRestrictionModel,
      Iso.trans_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
    exact WeilConjectures.upperModel_unit R j N
  have h := WeilConjectures.normalizedTransport
    ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight (openSquarePullbackModel A j).symm)
    (sfIntrinsicExtensionByZeroAdjunction j A)
    ((sfIntrinsicOpenAdjunction B j).ofNatIsoRight (openSquarePullbackModel B j).symm)
    (sfIntrinsicExtensionByZeroAdjunction j B)
    (Iso.refl _) (Iso.refl _)
    (WeilConjectures.compactSupportOpenRestrictionModel A j)
    (WeilConjectures.compactSupportOpenRestrictionModel B j)
    (proEtaleCoefficientRestrictScalars X φ) (proEtaleCoefficientRestrictScalars Z φ)
    (WeilConjectures.compactSupportScalarPullback j φ)
    (sfOpenRestrictionCoefficientSquare j φ).hom (sfOpenRestriction j φ).hom
    (by intro N; simpa using hu A N) (by intro N; simpa using hu B N)
    (WeilConjectures.compactSupportOpenRestrictionModel_scalar j φ)
    (sfOpenRestriction_normalized_unique j φ).1 M
  dsimp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app] at h
  simp only [Category.id_comp] at h
  rw [(proEtaleCoefficientRestrictScalars Z φ).map_id] at h
  exact h

end AlgebraicGeometry.ProEtale
