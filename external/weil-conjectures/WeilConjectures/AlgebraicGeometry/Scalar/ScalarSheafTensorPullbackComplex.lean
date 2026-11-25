/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Upper.UpperStarSingleTensorRepresentative

/-!
# The ordinary scalar tensor pullback square on complexes

## References

* Stacks 07A4
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

private theorem lift_complex_square
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive H]
    (F : C ⥤ E) (V : C ⥤ D) (U : D ⥤ C) (G : D ⥤ H) (R : H ⥤ E) (W : E ⥤ H)
    {T : C ⥤ C} {S : E ⥤ E}
    [F.Additive] [V.Additive] [U.Additive] [G.Additive] [R.Additive] [W.Additive]
    [T.Additive] [S.Additive]
    (τ : T ⟶ V ⋙ U) (σ : S ⟶ W ⋙ R)
    (χ : U ⋙ F ≅ G ⋙ R) (e : V ⋙ G ≅ F ⋙ W) (t : T ⋙ F ≅ F ⋙ S)
    (h : ∀ X, F.map (τ.app X) ≫ χ.hom.app (V.obj X) ≫ R.map (e.hom.app X) =
      t.hom.app X ≫ σ.app (F.obj X)) (P : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P) ≫
      (Functor.mapHomologicalComplexCompIso χ (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ R)) (.up ℤ)).symm).hom.app
          ((V.mapHomologicalComplex (.up ℤ)).obj P) ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ W)) (.up ℤ)).symm).hom.app P) =
    (Functor.mapHomologicalComplexCompIso t (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ S)) (.up ℤ)).symm).hom.app P ≫
        (NatTrans.mapHomologicalComplex σ (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  ext i
  change F.map (τ.app (P.X i)) ≫ (χ.hom.app (V.obj (P.X i)) ≫ 𝟙 _) ≫
      R.map (e.hom.app (P.X i) ≫ 𝟙 _) =
    (t.hom.app (P.X i) ≫ 𝟙 _) ≫ σ.app (F.obj (P.X i))
  simpa only [Category.comp_id] using h (P.X i)

/-- The ordinary balancing/pullback square applied degreewise to a complex. -/
theorem scalarSheafTensorPullbackComplex_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (scalarSheafTensorTransformation φ W)
          (.up ℤ)).app P) ≫
      (Functor.mapHomologicalComplexCompIso (upperStarRestrictScalarsIsoSheaf φ f) (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl
          (upperStar (ModuleCat.{u + 1} B) f ⋙ Sheaf.restrictScalars Z.smallEtaleTopology φ))
          (.up ℤ)).symm).hom.app
        (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((Sheaf.restrictScalars Z.smallEtaleTopology φ).mapHomologicalComplex (.up ℤ)).map
        ((scalarSheafPullbackComplexIso φ f).hom.app P) =
    (Functor.mapHomologicalComplexCompIso
        (upperStarTensorSingleIso A f (scalarCoefficientSheafPullbackIso φ f)) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl
        (upperStar (ModuleCat.{u + 1} A) f ⋙ tensorRight (scalarCoefficientSheaf φ Z)))
        (.up ℤ)).symm).hom.app P ≫
      (NatTrans.mapHomologicalComplex (scalarSheafTensorTransformation φ Z) (.up ℤ)).app
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact lift_complex_square (upperStar (ModuleCat.{u + 1} A) f)
    (ProEtale.etaleSheafExtendScalars φ W) (Sheaf.restrictScalars W.smallEtaleTopology φ)
    (upperStar (ModuleCat.{u + 1} B) f) (Sheaf.restrictScalars Z.smallEtaleTopology φ)
    (ProEtale.etaleSheafExtendScalars φ Z)
    (scalarSheafTensorTransformation φ W) (scalarSheafTensorTransformation φ Z)
    (upperStarRestrictScalarsIsoSheaf φ f) (scalarSheafPullbackIso φ f)
    (upperStarTensorSingleIso A f (scalarCoefficientSheafPullbackIso φ f))
    (scalarSheafTensorPullback_square φ f) P

end AlgebraicGeometry.Etale
