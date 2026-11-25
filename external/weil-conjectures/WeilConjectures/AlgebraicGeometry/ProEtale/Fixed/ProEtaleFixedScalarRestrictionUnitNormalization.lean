/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # The complex-unit normalization of fixed-scalar restriction and direct image

## References

* Stacks Tags 0D6E and 07A6, the factorization of the derived adjunction mate
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem unitQ_eq_homotopy
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (J : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ J = F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj J) := by
  change 𝟙 _ ≫ F.rightDerivedFunctorUnit.app _ ≫ F.rightDerivedFunctor.map (𝟙 _) = _
  erw [F.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  rfl

namespace AlgebraicGeometry.ProEtale

/-- The underived fixed-scalar comparison is the identity comparison on the underlying
restriction/direct-image functors. -/
theorem fixedScalarRestrictionDirectImageUnderived_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    fixedScalarRestrictionDirectImageUnderived φ f = Iso.refl _ := by
  ext M
  rfl

/-- The inverse fixed-scalar direct-image comparison is normalized by the canonical
right-derived units on all complexes. -/
theorem fixedScalarRestrictionDirectImage_unitQ_factors
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ) :
    (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorUnitQ K) ≫
      (fixedScalarRestrictionDirectImage φ f).inv.app (DerivedCategory.Q.obj K) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactors.hom.app K) =
    (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
          (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (fixedScalarRestrictionDirectImageUnderived φ f).hom (.up ℤ)).app K) ≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorUnitQ
        ((Functor.mapHomologicalComplex
          (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ) (.up ℤ)).obj K) := by
  simpa only [fixedScalarRestrictionDirectImage_inv, unitQ_eq_homotopy] using
    fixedScalarRestrictionDirectImageMap_factors φ f K

end AlgebraicGeometry.ProEtale
