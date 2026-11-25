/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData

/-!
# The exact restriction and geometric representative square

## References

* Stacks 07A4 and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar lowerStar

/-- Exact restriction commutes with geometric representatives, with the ordinary
restriction/pullback square as its complex representative. -/
theorem scalarRestrictionPullbackIso_geometric_representative
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ) :
    (scalarRestrictionPullbackIso φ f).hom.app (DerivedCategory.Q.obj P) ≫
        (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
          (scalarGeometricRepresentative B f P) ≫
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryFactors.hom.app
          (((upperStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj P) =
      L(upperStar (ModuleCat.{u + 1} A) f).map
          ((Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryFactors.hom.app P) ≫
        scalarGeometricRepresentative A f
          (((Sheaf.restrictScalars W.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
              (upperStarRestrictScalarsIsoSheaf φ f) (.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl
              (upperStar (ModuleCat.{u + 1} B) f ⋙
                Sheaf.restrictScalars Z.smallEtaleTopology φ)) (.up ℤ)).symm).hom.app P) := by
  apply (cancel_epi (L(upperStar (ModuleCat.{u + 1} A) f).map
    ((Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryFactors.inv.app P))).1
  have h := scalarRestrictionPullbackIso_representative φ f P
  rw [reassoc_of% h]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Etale
