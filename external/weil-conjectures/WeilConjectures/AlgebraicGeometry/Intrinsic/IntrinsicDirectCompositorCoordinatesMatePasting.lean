/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDirectComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicConjugateComparisonTransport

/-! Fixed-scalar intermediate for the intrinsic direct compositor calculation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

noncomputable def sfTransportRight
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁]
    [Category D₀] [Category D₁]
    (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {R : C₁ ⥤ C₀} {R' : D₁ ⥤ D₀}
    (b : (f.inverse ⋙ R ⋙ e.functor) ≅ R') :
    R' ⋙ e.inverse ≅ f.inverse ⋙ R :=
  Functor.isoWhiskerRight b.symm e.inverse ≪≫
    Functor.isoWhiskerLeft (f.inverse ⋙ R) e.unitIso.symm

/-- The ambient mate expression after returning to intrinsic coordinates. -/
@[irreducible] noncomputable def sfIntrinsicAmbientIntermediate
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective] :
    (proEtaleConstantDerivedDirectImage g A).obj
        ((proEtaleConstantDerivedDirectImage f A).obj
          ((sfIntrinsicDerivedEquivalence X A).functor.obj (DerivedCategory.Q.obj I))) ⟶
      ((sfIntrinsicDerivedEquivalence Z A).functor.obj
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj I))) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let eZ := sfIntrinsicDerivedEquivalence Z A
  let eY := sfIntrinsicDerivedEquivalence Y A
  let eX := sfIntrinsicDerivedEquivalence X A
  let ag0 := derivedUpperStarLowerStarAdjunction B g
  let af0 := derivedUpperStarLowerStarAdjunction B f
  let at0 := derivedUpperStarLowerStarAdjunction B (f ≫ g)
  let bg : (eY.inverse ⋙ (lowerStar B g).rightDerivedFunctor ⋙ eZ.functor) ≅
      proEtaleConstantDerivedDirectImage g A :=
    Functor.isoWhiskerLeft eY.inverse
      (sfIntrinsicDerivedDirectImageComparison g A).symm ≪≫
      Functor.isoWhiskerRight eY.counitIso _
  let bf : (eX.inverse ⋙ (lowerStar B f).rightDerivedFunctor ⋙ eY.functor) ≅
      proEtaleConstantDerivedDirectImage f A :=
    Functor.isoWhiskerLeft eX.inverse
      (sfIntrinsicDerivedDirectImageComparison f A).symm ≪≫
      Functor.isoWhiskerRight eX.counitIso _
  let N := eX.functor.obj (DerivedCategory.Q.obj I)
  let q := (sfTransportRight eZ eY bg).hom.app
      ((proEtaleConstantDerivedDirectImage f A).obj N) ≫
    (lowerStar B g).rightDerivedFunctor.map
      ((sfTransportRight eY eX bf).hom.app N) ≫
    ((conjugateEquiv (ag0.comp af0) at0
      (leftDerivedUpperStarComp B f g).hom).app (eX.inverse.obj N))
      ≫ (lowerStar B (f ≫ g)).rightDerivedFunctor.map
        (eX.unitIso.inv.app (DerivedCategory.Q.obj I))
  simpa only [Functor.comp_obj, Functor.id_obj, eX, N] using (eZ.counitIso.inv.app
      ((proEtaleConstantDerivedDirectImage g A).obj
        ((proEtaleConstantDerivedDirectImage f A).obj N)) ≫
    eZ.functor.map q)

/-- The first normalization identifies the pasted comparison with the intermediate. -/
theorem sfIntrinsicDirectCompositorCoordinates_ambient_normalization
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective] :
    (proEtaleConstantDerivedDirectImage g A).map
        ((sfIntrinsicDerivedDirectImageComparison f A).hom.app (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedDirectImageComparison g A).hom.app
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedEquivalence Z A).functor.map
        ((conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).comp
            (derivedUpperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f))
          (derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g))
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g)).hom.app
          (DerivedCategory.Q.obj I)) =
      sfIntrinsicAmbientIntermediate A f g I  := by
  simpa [sfIntrinsicAmbientIntermediate, sfIntrinsicAmbientCoordinate,
    sfIntrinsicTransportRight, sfTransportRight] using
    (sfIntrinsicDirectComparisonTransport A f g I
      (leftDerivedUpperStarComp
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g))

/-- The intermediate is the composite-adjunction coordinate. -/
theorem sfIntrinsicDirectCompositorCoordinates_ambient_to_intrinsic
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective] :
    sfIntrinsicAmbientIntermediate A f g I =
      (conjugateIsoEquiv
        ((sfIntrinsicConstantModuleAdjunction g A).mapDerivedCategoryRightDerivedAdjunction.comp
          (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction)
        (sfIntrinsicConstantModuleAdjunction (f ≫ g) A).mapDerivedCategoryRightDerivedAdjunction
        (sfIntrinsicDerivedPullbackComp A f g)).hom.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedDirectImageComparison (f ≫ g) A).hom.app
        (DerivedCategory.Q.obj I)   := by
  have h := sfIntrinsicConjugateComparisonTransport A f g I
  calc
    sfIntrinsicAmbientIntermediate A f g I =
        sfIntrinsicAmbientCoordinate A f g I
          (leftDerivedUpperStarComp
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g) := by
      simp [sfIntrinsicAmbientIntermediate, sfIntrinsicAmbientCoordinate,
        sfTransportRight, sfIntrinsicTransportRight]
    _ = _ := by
      rw [h]
      simp

end AlgebraicGeometry.Scheme
