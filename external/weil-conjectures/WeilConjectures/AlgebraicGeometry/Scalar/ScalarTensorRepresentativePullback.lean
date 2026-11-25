/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarTensorRepresentativeCalculus

/-!
# Scalar tensor representatives commute with pullback

## References

* Stacks 07A4 and 0FPH
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

/-- The tensor counit square in the scalar tensor functor's endpoint convention. -/
theorem scalarTensorRepresentative_pullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
          (DerivedCategory.Q.obj P)).app (scalarCoefficient φ W) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
          (L(upperStar (ModuleCat.{u + 1} A) f).obj (DerivedCategory.Q.obj P))).map
          (scalarCoefficientPullbackIso φ f).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).flip.obj (scalarCoefficient φ Z)).map
          (scalarGeometricRepresentative A f P) ≫
        scalarTensorRepresentative φ Z
          (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
      L(upperStar (ModuleCat.{u + 1} A) f).map (scalarTensorRepresentative φ W P) ≫
        scalarGeometricRepresentative A f
          (((tensorRight (scalarCoefficientSheaf φ W)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
              (upperStarTensorSingleIso A f (scalarCoefficientSheafPullbackIso φ f)) (.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl
              (upperStar (ModuleCat.{u + 1} A) f ⋙
                tensorRight (scalarCoefficientSheaf φ Z))) (.up ℤ)).symm).hom.app P) := by
  have h := upperStar_single_tensor_representative A f (scalarCoefficientSheafPullbackIso φ f) P
  dsimp only [scalarTensorRepresentative, scalarCoefficient, scalarTensorModelFunctor,
    derivedTensor, eqToIso.hom] at h ⊢
  simpa only [eqToHom_refl, NatTrans.id_app, Category.id_comp, Category.assoc,
    scalarCoefficientSinglePullbackIso_eq] using h

end AlgebraicGeometry.Etale
