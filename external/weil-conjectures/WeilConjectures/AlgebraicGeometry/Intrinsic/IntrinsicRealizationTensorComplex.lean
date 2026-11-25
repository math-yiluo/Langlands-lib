/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRealization

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce

/-! # Total tensor and intrinsic coefficient realization

## References

* Stacks Project, Modules on Sites, Tag 0GMW
* Cohomology on Sites, Tag 06YN
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

private noncomputable instance constModuleMonoidal (T : Scheme.{u}) (A : Type u) [CommRing A] :
    MonoidalCategory (PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u + 1}
    (((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))) ⋙
      forget₂ CommRingCat RingCat)))

private theorem moduleSheafificationUnit_isIso
    (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (P : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    let E := finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)
    let S := PresheafOfModules.sheafification.{u + 1} (finiteCoefficientIntrinsicScalarMap T A)
    IsIso (S.map (E.map (toSheafify (Scheme.ProEt.topology T) P))) := by
  dsimp only
  rw [← MorphismProperty.isomorphisms.iff]
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification.{u + 1} (finiteCoefficientIntrinsicScalarMap T A))) _
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  change (Scheme.ProEt.topology T).W
    (Functor.whiskerRight (toSheafify (Scheme.ProEt.topology T) P)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1}))
  let : (Scheme.ProEt.topology T).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.forget₂CoinduceAdj (ULift.{u + 1, u} A))
  exact (Scheme.ProEt.topology T).W_of_preservesSheafification _ _
    ((Scheme.ProEt.topology T).W_toSheafify P)

private theorem intrinsicTensorNatIso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    let F := finiteCoefficientIntrinsicRealization T A
    letI := SheafOfModules.monoidalCategory (Scheme.proEtaleConstantRing T A)
    Nonempty (tensor _ ⋙ F ≅ F.prod F ⋙ tensor _) := by
  let J := Scheme.ProEt.topology T
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let E := finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)
  let S := PresheafOfModules.sheafification.{u + 1} (finiteCoefficientIntrinsicScalarMap T A)
  let U := sheafToPresheaf J B
  let L := presheafToSheaf J B
  let F := finiteCoefficientIntrinsicRealization T A
  let := SheafOfModules.monoidalCategory (Scheme.proEtaleConstantRing T A)
  let t : E ⋙ S ⟶ L ⋙ F :=
    Functor.whiskerRight (sheafificationAdjunction J B).unit (E ⋙ S)
  have : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    exact moduleSheafificationUnit_isIso T A P
  let h : E ⋙ S ≅ L ⋙ F := asIso t
  let c := asIso (sheafificationAdjunction J B).counit
  let e : U.prod U ⋙ tensor _ ⋙ L ≅ tensor _ :=
    Functor.isoWhiskerLeft (U.prod U) (Functor.Monoidal.μNatIso L).symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod c c) (tensor _)
  let eE : tensor _ ⋙ E ≅ E.prod E ⋙ tensor _ := Iso.refl _
  obtain ⟨eS, _⟩ := PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
    (finiteCoefficientIntrinsicScalarMap T A)
  refine ⟨(Functor.isoWhiskerRight e F).symm ≪≫
    Functor.isoWhiskerLeft (U.prod U ⋙ tensor _) h.symm ≪≫
    Functor.isoWhiskerLeft (U.prod U) (Functor.isoWhiskerRight eE S) ≪≫
    Functor.isoWhiskerLeft ((U ⋙ E).prod (U ⋙ E)) eS.symm⟩

private theorem tensorComplexTransportAux
    {C D : Type*} [Category.{v} C] [Category.{w} D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalCategory D] [(curriedTensor D).PreservesZeroMorphisms]
    [∀ X, ((curriedTensor D).obj X).PreservesZeroMorphisms]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (V W : CochainComplex C ℤ) :
    Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor V W (curriedTensor C)) ≅
        CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj V)
          ((F.mapHomologicalComplex (.up ℤ)).obj W) (curriedTensor D)) := by
  let τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) :=
    { app := fun X ↦
        { app := fun Y ↦ e.hom.app (X, Y)
          naturality := by
            intro Y Y' g
            simpa using e.hom.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, g) }
      naturality := by
        intro X X' f
        ext Y
        simpa using e.hom.naturality (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y) }
  have (X Y : C) : IsIso ((τ.app X).app Y) := (e.app (X, Y)).isIso_hom
  exact ⟨asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) V W)⟩

/-- Canonical coefficient realization commutes with ordinary total tensor complexes. -/
theorem intrinsic_realization_tensor_complex_iso
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u})
    (V W : CochainComplex
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    let F := finiteCoefficientIntrinsicRealization T A
    letI := SheafOfModules.monoidalCategory (Scheme.proEtaleConstantRing T A)
    Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor V W (CategoryTheory.MonoidalCategory.curriedTensor _)) ≅
        CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj V)
          ((F.mapHomologicalComplex (.up ℤ)).obj W)
          (CategoryTheory.MonoidalCategory.curriedTensor _)) := by
  let F := finiteCoefficientIntrinsicRealization T A
  let : F.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact T A).1
  let := SheafOfModules.monoidalCategory (Scheme.proEtaleConstantRing T A)
  obtain ⟨e⟩ := intrinsicTensorNatIso T A
  exact tensorComplexTransportAux F e V W

end AlgebraicGeometry.ProEtale
