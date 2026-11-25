/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDirectCompositorCoordinatesKInjective

/-! # Coefficient realization of an ordinary direct-image compositor

## References

* Stacks 00YV and 03D3 (transport of the module adjunction), 07A5 and 07A6 (K-injective direct image
  and its adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

/-- The section-normalized coefficient realization preserves the ordinary direct-image
compositor. This is solely a comparison between the two presentations of one finite
coefficient category: it involves no coefficient sequence, evaluation, or system operation.
-/
private theorem natTrans_ext_of_kInjective
    {C D : Type*} [Category C] [Category D] [Abelian C]
    [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions C]
    {F G : DerivedCategory C ⥤ D} (α β : F ⟶ G)
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I)) : α = β := by
  ext X
  obtain ⟨I, hI, a, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    (DerivedCategory.Q.objPreimage X)
  let e : X ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map a)
  apply (cancel_mono (G.map e.hom)).mp
  rw [← α.naturality, ← β.naturality, h I]

theorem sfIntrinsicDirectCompositorCoordinates
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (J : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let af := (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
    let ag := (sfIntrinsicConstantModuleAdjunction g A).mapDerivedCategoryRightDerivedAdjunction
    let adjt := (sfIntrinsicConstantModuleAdjunction
      (f ≫ g) A).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleConstantDerivedDirectImage g A).map
        ((sfIntrinsicDerivedDirectImageComparison f A).hom.app J) ≫
      (sfIntrinsicDerivedDirectImageComparison g A).hom.app
        ((lowerStar B f).rightDerivedFunctor.obj J) ≫
      (sfIntrinsicDerivedEquivalence Z A).functor.map
        ((conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction B g).comp
            (derivedUpperStarLowerStarAdjunction B f))
          (derivedUpperStarLowerStarAdjunction B (f ≫ g))
          (leftDerivedUpperStarComp B f g)).hom.app J) =
    (conjugateIsoEquiv (ag.comp af) adjt
      (sfIntrinsicDerivedPullbackComp A f g)).hom.app
        ((sfIntrinsicDerivedEquivalence X A).functor.obj J) ≫
      (sfIntrinsicDerivedDirectImageComparison (f ≫ g) A).hom.app J := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let RX := sfIntrinsicDerivedEquivalence X A
  let RY := sfIntrinsicDerivedEquivalence Y A
  let RZ := sfIntrinsicDerivedEquivalence Z A
  let Cf := proEtaleConstantDerivedDirectImage f A
  let Cg := proEtaleConstantDerivedDirectImage g A
  let Ct := proEtaleConstantDerivedDirectImage (f ≫ g) A
  let Rf := (lowerStar B f).rightDerivedFunctor
  let Rg := (lowerStar B g).rightDerivedFunctor
  let Rt := (lowerStar B (f ≫ g)).rightDerivedFunctor
  let ef := sfIntrinsicDerivedDirectImageComparison f A
  let eg := sfIntrinsicDerivedDirectImageComparison g A
  let et := sfIntrinsicDerivedDirectImageComparison (f ≫ g) A
  let q := conjugateIsoEquiv
    ((derivedUpperStarLowerStarAdjunction B g).comp
      (derivedUpperStarLowerStarAdjunction B f))
    (derivedUpperStarLowerStarAdjunction B (f ≫ g))
    (leftDerivedUpperStarComp B f g)
  let d := conjugateIsoEquiv
    ((sfIntrinsicConstantModuleAdjunction g A).mapDerivedCategoryRightDerivedAdjunction.comp
      (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction)
    (sfIntrinsicConstantModuleAdjunction (f ≫ g) A).mapDerivedCategoryRightDerivedAdjunction
    (sfIntrinsicDerivedPullbackComp A f g)
  let α : RX.functor ⋙ Cf ⋙ Cg ⟶ Rt ⋙ RZ.functor :=
    { app := fun J => Cg.map (ef.hom.app J) ≫ eg.hom.app (Rf.obj J) ≫
        RZ.functor.map (q.hom.app J)
      naturality := by
        intro J K h
        dsimp only [Functor.comp_obj, Functor.comp_map, NatTrans.comp_app]
        simp only [Category.assoc]
        change Cg.map (Cf.map (RX.functor.map h)) ≫ Cg.map (ef.hom.app K) ≫
            eg.hom.app (Rf.obj K) ≫ RZ.functor.map (q.hom.app K) =
          Cg.map (ef.hom.app J) ≫ eg.hom.app (Rf.obj J) ≫
            RZ.functor.map (q.hom.app J) ≫ RZ.functor.map (Rt.map h)
        have hef : Cf.map (RX.functor.map h) ≫ ef.hom.app K =
            ef.hom.app J ≫ RY.functor.map (Rf.map h) := by
          simpa only [Functor.comp_map] using ef.hom.naturality h
        have heg : Cg.map (RY.functor.map (Rf.map h)) ≫ eg.hom.app (Rf.obj K) =
            eg.hom.app (Rf.obj J) ≫ RZ.functor.map (Rg.map (Rf.map h)) := by
          simpa only [Functor.comp_map] using eg.hom.naturality (Rf.map h)
        have heg' : Cg.map (ef.hom.app J) ≫
              Cg.map (RY.functor.map (Rf.map h)) ≫ eg.hom.app (Rf.obj K) =
            Cg.map (ef.hom.app J) ≫ eg.hom.app (Rf.obj J) ≫
              RZ.functor.map (Rg.map (Rf.map h)) := by
          rw [heg]
        have hq : Rg.map (Rf.map h) ≫ q.hom.app K =
            q.hom.app J ≫ Rt.map h := by
          simpa only [Functor.comp_map] using q.hom.naturality h
        have hcg := (Cg.map_comp (Cf.map (RX.functor.map h)) (ef.hom.app K)).symm
        rw [reassoc_of% hcg, hef, Functor.map_comp]
        simp only [Category.assoc]
        rw [reassoc_of% heg']
        rw [← RZ.functor.map_comp, hq, RZ.functor.map_comp] }
  let β : RX.functor ⋙ Cf ⋙ Cg ⟶ Rt ⋙ RZ.functor :=
    { app := fun J => d.hom.app (RX.functor.obj J) ≫ et.hom.app J
      naturality := by
        intro J K h
        dsimp only [Functor.comp_obj, Functor.comp_map, NatTrans.comp_app]
        have hd := d.hom.naturality (RX.functor.map h)
        have het : Ct.map (RX.functor.map h) ≫ et.hom.app K =
            et.hom.app J ≫ RZ.functor.map (Rt.map h) := by
          simpa only [Functor.comp_map] using et.hom.naturality h
        have het' :
              (proEtaleConstantModuleDirectImage (f ≫ g) A).rightDerivedFunctor.map
                  (RX.functor.map h) ≫ et.hom.app K =
                et.hom.app J ≫ RZ.functor.map (Rt.map h) := by
          simpa only [Ct, Rt] using het
        have hd' : Cg.map (Cf.map (RX.functor.map h)) ≫
              d.hom.app (RX.functor.obj K) =
            d.hom.app (RX.functor.obj J) ≫
              (proEtaleConstantModuleDirectImage (f ≫ g) A).rightDerivedFunctor.map
                (RX.functor.map h) := by
          simpa only [Functor.comp_map] using hd
        calc
          _ = d.hom.app (RX.functor.obj J) ≫
              (proEtaleConstantModuleDirectImage (f ≫ g) A).rightDerivedFunctor.map
                (RX.functor.map h) ≫ et.hom.app K := by
            rw [reassoc_of% hd']
          _ = _ := by
            rw [Category.assoc, het'] }
  have hab : α = β := by
    apply natTrans_ext_of_kInjective
    intro I hI
    have h := sfIntrinsicDirectCompositorCoordinates_kInjective A f g I
    simpa only [α, β, RX, RY, RZ, Cf, Cg, Ct, Rf, Rg, Rt, ef, eg, et, q, d,
      Functor.comp_obj, Functor.comp_map, NatTrans.comp_app] using h
  have h := congr_app hab J
  simpa only [α, β, RX, RY, RZ, Cf, Cg, Ct, Rf, Rg, Rt, ef, eg, et, q, d,
    Functor.comp_obj, Functor.comp_map, NatTrans.comp_app] using h

end AlgebraicGeometry.Scheme
