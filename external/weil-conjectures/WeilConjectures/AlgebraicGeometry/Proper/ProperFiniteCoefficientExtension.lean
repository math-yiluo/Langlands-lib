/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtensionCore

/-! # Proper finite coefficient extension

The theorem records the canonical unbounded coefficient-change comparison, its
adjunction normalization, and the identification after restriction of scalars
with the coefficient-first proper projection morphism.

## References

* Stacks Project, Tag 0GL6, proper case
* Stacks Project, Tag 0GL6, with the counit-transpose normalization of Tag 0B56 and the direct-image
  composition comparison of Tag 0D6E
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Canonical unbounded proper direct-image comparison for a finite coefficient extension. -/
theorem properFiniteCoefficientExtension
    {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsNoetherian X] [IsNoetherian Y] :
    (∀ L : DerivedCategoryModule R X,
      IsIso ((scalarMate φ f).app L)) ∧
    (∀ L : DerivedCategoryModule R X,
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app
          (scalarCoefficient φ Y)).app
            (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        (scalarTensorIso φ Y).inv.app
          (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
          ((scalarMate φ f).app L) ≫
        (scalarRestrictionDirectImageMap φ f).app
          ((scalarExtension φ X).obj L) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map
          ((scalarTensorIso φ X).hom.app L ≫
            ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app L).app
              (scalarCoefficient φ X)) =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app
          (scalarCoefficient φ Y)).app
            (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) f).app L).app
          (scalarCoefficient φ Y) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map
          (((derivedTensor (ModuleCat.{u + 1} R) X).obj L).map
              ((scalarCoefficientPullbackIso φ f).hom) ≫
            ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app L).app
              (scalarCoefficient φ X))) ∧
    (∀ L : DerivedCategoryModule R X,
      (scalarMate φ f).app L =
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv
          ((scalarExtension φ Y).obj
            (R((f)_*[ModuleCat.{u + 1} R]).obj L))
          ((scalarExtension φ X).obj L)
          ((scalarPullbackIso φ f).hom.app
              (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
            (scalarExtension φ X).map
              ((derivedUpperStarLowerStarAdjunction
                (ModuleCat.{u + 1} R) f).counit.app L))) := by
  obtain ⟨h₁, h₂⟩ := properFiniteCoefficientExtensionCore φ f
  refine ⟨h₁, h₂, ?_⟩
  intro L
  unfold scalarMate
  let adjR := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f
  let adjA := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  change ((mateEquiv adjR adjA
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ f).hom)).app L) = _
  apply (adjA.homEquiv
    ((scalarExtension φ Y).obj (R((f)_*[ModuleCat.{u + 1} R]).obj L))
    ((scalarExtension φ X).obj L)).symm.injective
  rw [adjA.homEquiv_counit, Equiv.symm_apply_apply]
  exact mateEquiv_counit adjR adjA
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ f).hom) L

end AlgebraicGeometry.Etale
