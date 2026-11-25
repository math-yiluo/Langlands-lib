/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.PointModelRestrictionModule
import all WeilConjectures.AlgebraicGeometry.ConstantCoefficientChartPullback
import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs

/-! # Invariance of the coefficient slice model under internal restriction isomorphisms

Source: Stacks, Modules on Sites, Tag 03CY; Sites, Tag 00YV;
More on Morphisms, Tags 094T and 0951; Sites, Section 00XZ.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar

private theorem equivalence_comp
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (F : A ⥤ B) (G : B ⥤ C) (hF : F.IsEquivalence) (hG : G.IsEquivalence) :
    (F ⋙ G).IsEquivalence := by
  let := hF
  let := hG
  exact CategoryTheory.Functor.isEquivalence_trans F G

private theorem square_of_right_square
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {L : A ⥤ B} {R : B ⥤ A} {P : C ⥤ D} {Q : D ⥤ C}
    (a : L ⊣ R) (b : P ⊣ Q) (E : A ≌ C) (G : B ≌ D)
    (h : R ⋙ E.functor ≅ G.functor ⋙ Q) :
    Nonempty (L ⋙ G.functor ≅ E.functor ⋙ P) := by
  let h₁ : (G.inverse ⋙ R) ⋙ E.functor ≅ Q :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G.inverse h ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight G.counitIso Q ≪≫ Functor.leftUnitor Q
  let h₂ : (Q ⋙ E.inverse) ⋙ E.functor ≅ Q :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q E.counitIso ≪≫
      Functor.rightUnitor Q
  let r := ((Functor.FullyFaithful.ofFullyFaithful E.functor).whiskeringRight _)
    |>.preimageIso (h₁ ≪≫ h₂.symm)
  exact ⟨((conjugateIsoEquiv (a.comp G.toAdjunction) (E.toAdjunction.comp b)).symm r).symm⟩

private theorem composite_transport
    {A B C D E F : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    (L : A ⥤ B) (K : B ⥤ C) (H : A ⥤ C)
    (I : A ⥤ D) (J : B ⥤ E) (T : C ⥤ F) (P : D ⥤ E) (Q : E ⥤ F)
    (ec : H ≅ L ⋙ K) (ef : L ⋙ J ≅ I ⋙ P) (eg : K ⋙ T ≅ J ⋙ Q)
    {N M : A} (h : Nonempty (H.obj N ≅ H.obj M)) :
    Nonempty (Q.obj (P.obj (I.obj N)) ≅ Q.obj (P.obj (I.obj M))) := by
  obtain ⟨e⟩ := h
  let e' := T.mapIso ((ec.app N).symm ≪≫ e ≪≫ ec.app M)
  let tN := eg.app (L.obj N) ≪≫ Q.mapIso (ef.app N)
  let tM := eg.app (L.obj M) ≪≫ Q.mapIso (ef.app M)
  exact ⟨tN.symm ≪≫ e' ≪≫ tM⟩

private theorem smallPushforward_equivalence (X : Scheme.{u})
    (B : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    (SheafOfModules.pushforward.{u + 1} (F := AsSmall.down)
      (𝟙 ((AsSmall.down.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (Scheme.ProEt.topology X)).obj B))).IsEquivalence := by
  let e := (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm
  let : e.inverse.IsContinuous (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)  := by
    change (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, u} X).IsContinuous
      (Scheme.ProEt.topology X) _
    exact inferInstanceAs
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
        (Scheme.ProEt.topology X)
        ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.inducedTopology
          (Scheme.ProEt.topology X)))
  let : e.functor.IsContinuous (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsContinuous
      _ _
    infer_instance
  let E := SheafOfModules.pushforwardPushforwardEquivalence.{u + 1}
    (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (K := Scheme.ProEt.topology X) e (𝟙 _)
    (show B ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)).obj
        ((e.functor.sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (Scheme.ProEt.topology X)).obj B) from 𝟙 _)
    (by ext V; simp [e, AsSmall.equiv]; rfl)
    (by
      ext V x
      change B.obj.map (𝟙 _) x = x
      simp)
  exact E.isEquivalence_functor

private theorem scalarRestriction_equivalence
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {R S : Sheaf J RingCat.{u + 1}} (c : S ≅ R) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence := by
  let e : C ≌ C := CategoryTheory.Equivalence.refl
  let : e.functor.IsContinuous J J :=
    inferInstanceAs ((𝟭 C).IsContinuous J J)
  let : e.inverse.IsContinuous J J :=
    inferInstanceAs ((𝟭 C).IsContinuous J J)
  let E := SheafOfModules.pushforwardPushforwardEquivalence.{u + 1}
    (S := S) (R := R) e c.hom c.inv
    (by
      ext V x
      dsimp [e, CategoryTheory.Equivalence.refl]
      rw [R.obj.map_id]
      exact congrArg (fun f ↦ f.hom.app V x) c.inv_hom_id.symm)
    (by
      ext V x
      dsimp [e, CategoryTheory.Equivalence.refl]
      rw [S.obj.map_id]
      exact congrArg (fun f ↦ f.hom.app V x) c.hom_inv_id)
  exact E.isEquivalence_functor

private noncomputable def sectionFixedModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ X) ⥤
      Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} k) :=
  SheafOfModules.pushforward (F := AsSmall.down) (𝟙 _) ⋙
    ConstantCompletion.res c.hom ⋙ coefficientModelFixedScalars _ k

private noncomputable def fixedModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :=
  (InternalModuleOperations.equivalence Λ X).functor ⋙ sectionFixedModel Λ X k c

private theorem fixedModel_equivalence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    (fixedModel Λ X k c).IsEquivalence := by
  unfold fixedModel sectionFixedModel
  exact equivalence_comp (InternalModuleOperations.equivalence Λ X).functor _
    (InternalModuleOperations.equivalence Λ X).isEquivalence_functor
    (equivalence_comp _ _
      (smallPushforward_equivalence X (InternalModuleOperations.ring Λ X))
      (equivalence_comp (ConstantCompletion.res c.hom) (coefficientModelFixedScalars _ k)
        (scalarRestriction_equivalence _
          ((sheafCompose (Scheme.coefficientProEtaleModelTopology.{u, u} X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c))
        (coefficientModelFixedScalars_isEquivalence _ k)))

private theorem fixedModel_pullback_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    ∃ d : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k ≅
        smallRing Y (condensedRingObj Λ Y),
      Nonempty (CondensedRing.upperStar Λ f ⋙ fixedModel Λ Y k d ≅
        fixedModel Λ X k c ⋙ Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k) := by
  obtain ⟨d, hd⟩ := exists_constant_coefficient_chart_pullback Λ f k c
  let R := (Scheme.coefficientProEtaleModelBaseChange.{u, u} f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} k) (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
  let H : InternalModuleOperations.lowerStar Λ f ⋙ sectionFixedModel Λ X k c ≅
      sectionFixedModel Λ Y k d ⋙ R := by
    refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun V ↦ ?_) ?_)) ?_
    · refine ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)
      ext x
      let y : M.val.obj ((InternalModuleOperations.siteMap f).op.obj
        (AsSmall.down.op.obj V)) := x
      change (d.hom.hom.app
          ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)).hom
          ((SheafOfModules.constantCoefficientUnit
            (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k).app
              ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V) a) •
            (show M.val.obj ((InternalModuleOperations.siteMap f).op.obj
              (AsSmall.down.op.obj V)) from y) =
        ((InternalModuleOperations.coefficientMap Λ f).hom.app (AsSmall.down.op.obj V)).hom
          ((c.hom.hom.app V).hom ((SheafOfModules.constantCoefficientUnit
            (Scheme.coefficientProEtaleModelTopology.{u, u} X) k).app V a)) • y
      exact congrArg (fun r : (InternalModuleOperations.ring Λ Y).obj.obj
          ((InternalModuleOperations.siteMap f).op.obj (AsSmall.down.op.obj V)) ↦
        r • (show M.val.obj ((InternalModuleOperations.siteMap f).op.obj
          (AsSmall.down.op.obj V)) from x)) (hd V a).symm
    · intro V W q
      ext x
      rfl
    · intro M N q
      ext V x
      rfl
  have h : CondensedRing.lowerStar Λ f ⋙ fixedModel Λ X k c ≅ fixedModel Λ Y k d ⋙ R :=
    Functor.isoWhiskerRight (InternalModuleOperations.lowerComparison Λ f)
      (sectionFixedModel Λ X k c) ≪≫
        Functor.isoWhiskerLeft (InternalModuleOperations.equivalence Λ Y).functor H
  have := fixedModel_equivalence Λ X k c
  have := fixedModel_equivalence Λ Y k d
  let E := (fixedModel Λ X k c).asEquivalence
  let G := (fixedModel Λ Y k d).asEquivalence
  exact ⟨d, square_of_right_square (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.coefficientProEtaleModelBaseChange.{u, u} f) (ModuleCat.{u + 1} k)
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)) E G h⟩

private noncomputable def modelEquivalence (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} k) ≌
      Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} k) :=
  coefficientSiteSheafEquivalence X (ModuleCat.{u + 1} k)

private noncomputable def modelPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k ⋙
        (modelEquivalence Y k).inverse ≅
      (modelEquivalence X k).inverse ⋙ upperStar (ModuleCat.{u + 1} k) f := by
  let a := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, u} f) (ModuleCat.{u + 1} k)
    (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (Scheme.coefficientProEtaleModelTopology.{u, u} Y)).comp
      (modelEquivalence Y k).symm.toAdjunction
  let b := (modelEquivalence X k).symm.toAdjunction.comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} k) f)
  exact ((conjugateIsoEquiv a b).symm (Iso.refl _)).symm

private theorem slice_iso_of_model_pullback_iso {Y : Scheme.{u}}
    (k : Type (u + 1)) [CommRing k]
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y)
    (F G : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y) (ModuleCat.{u + 1} k))
    (h : Nonempty ((Scheme.coefficientProEtaleFixedModulePullback.{u, u}
        (AsSmall.down.obj U).hom k).obj F ≅
      (Scheme.coefficientProEtaleFixedModulePullback.{u, u}
        (AsSmall.down.obj U).hom k).obj G)) : Nonempty (F.over U ≅ G.over U) := by
  obtain ⟨e⟩ := h
  let W : Y.ProEt := AsSmall.down.obj U
  let e' : (upperStar (ModuleCat.{u + 1} k) W.hom).obj
        ((modelEquivalence Y k).inverse.obj F) ≅
      (upperStar (ModuleCat.{u + 1} k) W.hom).obj
        ((modelEquivalence Y k).inverse.obj G) :=
    ((modelPullbackIso W.hom k).app F).symm ≪≫
      (modelEquivalence W.left k).inverse.mapIso e ≪≫ (modelPullbackIso W.hom k).app G
  let t := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} k) W.hom W.prop
  let t' := (sheafToPresheaf _ _).mapIso
    ((t.app _).symm ≪≫ e' ≪≫ t.app _)
  let S : Over U ⥤ W.left.ProEt :=
    { obj V := by
        let T : Over W := Over.mk (AsSmall.down.map V.hom)
        exact (Scheme.ProEt.sliceTo Y W).obj T
      map q := MorphismProperty.Over.homMk q.left.down.left (by
        exact congrArg (fun r ↦ r.down.left) (Over.w q)) }
  let β : S ⋙ MorphismProperty.Over.map ⊤ W.prop ⋙ AsSmall.up ≅ Over.forget U :=
    NatIso.ofComponents (fun V ↦ AsSmall.up.mapIso
      (MorphismProperty.Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ (AsSmall.down.obj V.left).hom =
          (AsSmall.down.map V.hom).left ≫ W.hom
        exact (Category.id_comp _).trans (MorphismProperty.Over.w (AsSmall.down.map V.hom)).symm)))
      (by
        intro V V' q
        apply ULift.ext
        apply MorphismProperty.Over.Hom.ext
        change q.left.down.left ≫ 𝟙 _ = 𝟙 _ ≫ q.left.down.left
        simp only [Category.comp_id, Category.id_comp])
  refine ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso ?_⟩
  exact Functor.isoWhiskerRight (NatIso.op β) F.obj ≪≫
    Functor.isoWhiskerLeft S.op t' ≪≫
      (Functor.isoWhiskerRight (NatIso.op β) G.obj).symm

private noncomputable def modelReassociate (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {D : Type*} [Category* D] (K : ConstantCompletion.Mod (smallRing X R) ⥤ D) :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R).functor ⋙
      (SheafOfModules.pushforward (F := AsSmall.down) (𝟙 _) ⋙ K) ≅
        smallModules X R ⋙ K :=
  (Functor.associator _ _ _).symm

private noncomputable def fixedModelComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    fixedModel Λ X k c ≅ smallModules X (condensedRingObj Λ X) ⋙
      ConstantCompletion.res c.hom ⋙ coefficientModelFixedScalars _ k :=
  modelReassociate X (condensedRingObj Λ X)
    (ConstantCompletion.res c.hom ⋙ coefficientModelFixedScalars _ k)

private theorem model_iso_after_composite
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X))
    (N M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : Nonempty (pointModelRestriction Λ f N g ≅ pointModelRestriction Λ f M g)) :
    Nonempty ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} g k).obj
        ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
          ((fixedModel Λ X k c).obj N)) ≅
      (Scheme.coefficientProEtaleFixedModulePullback.{u, u} g k).obj
        ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
          ((fixedModel Λ X k c).obj M))) := by
  change Nonempty ((CondensedRing.upperStar Λ (g ≫ f)).obj N ≅
    (CondensedRing.upperStar Λ (g ≫ f)).obj M) at h
  obtain ⟨cY, ⟨ef⟩⟩ := fixedModel_pullback_square Λ f k c
  obtain ⟨cZ, ⟨eg⟩⟩ := fixedModel_pullback_square Λ g k cY
  exact composite_transport (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ g)
    (CondensedRing.upperStar Λ (g ≫ f)) (fixedModel Λ X k c) (fixedModel Λ Y k cY)
    (fixedModel Λ Z k cZ) (Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k)
    (Scheme.coefficientProEtaleFixedModulePullback.{u, u} g k)
    (CondensedRing.upperStarComp Λ g f) ef eg h

private theorem slice_of_model_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X))
    (N M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y)
    (h : Nonempty
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} (AsSmall.down.obj U).hom k).obj
        ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
          ((fixedModel Λ X k c).obj N)) ≅
      (Scheme.coefficientProEtaleFixedModulePullback.{u, u} (AsSmall.down.obj U).hom k).obj
        ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
          ((fixedModel Λ X k c).obj M)))) :
    Nonempty (((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
      ((coefficientModelFixedScalars _ k).obj
        ((smallModules X (condensedRingObj Λ X) ⋙ ConstantCompletion.res c.hom).obj N))).over U ≅
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
        ((coefficientModelFixedScalars _ k).obj
          ((smallModules X (condensedRingObj Λ X) ⋙
            ConstantCompletion.res c.hom).obj M))).over U) := by
  obtain ⟨e⟩ := slice_iso_of_model_pullback_iso k U _ _ h
  let t := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (fixedModelComparison Λ X k c)
      (Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k))
    ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).overPullback (ModuleCat.{u + 1} k) U)
  exact ⟨(t.app N).symm ≪≫ e ≪≫ t.app M⟩

attribute [local irreducible] fixedModel sectionFixedModel modelEquivalence modelPullbackIso

/-- Reconstruction on the coefficient slice respects an isomorphism of internal inverse images.
This comparison concerns arbitrary modules; it has no finite presentation or point-module input.

Source: Stacks, Modules on Sites, Tag 03CY; Sites, Tag 00YV;
More on Morphisms, Tags 094T and 0951; Sites, Section 00XZ.
(auxiliary; not a blueprint node).

Proof: let Z be the underlying scheme of U and g its structural map to Y. Section
reconstruction identifies internal modules with modules over their section ring sheaves.
Transport this equivalence along the small-site equivalence. The inverse-image comparison
for section reconstruction identifies the resulting inverse image along g composed with f
with the ringed-site inverse image: both are left adjoints to the same sectionwise direct
image with its restricted scalar action. The cartesian coefficient comparison identifies
its pulled-back ring with the section ring of the coefficient on Z. Restricting scalars
along c commutes with this comparison, since on both sides the action is obtained by
precomposing with the pulled-back map c. The equivalence between modules over the constant
ring sheaf and sheaves of k-modules similarly commutes with inverse image, by uniqueness of
left adjoints to the identical sectionwise direct images. Finally weakly etale localization
identifies sheaves on Z with sheaves on the slice over U; the AsSmall equivalences give the
same identification on the coefficient-sized sites. Together these comparisons identify,
for each module Q on X, the displayed fixed-scalar sheaf on the slice with the reconstruction
of the internal inverse image of Q on Z. Apply this reconstruction functor to the given
isomorphism between the inverse images of N and M, and conjugate by the two comparisons.
No conservativity of inverse image, finiteness, or choice of a presentation is used.
-/
theorem coefficient_slice_iso_of_internal_restriction_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X))
    (N M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y)
    (h : Nonempty (pointModelRestriction Λ f N (AsSmall.down.obj U).hom ≅
      pointModelRestriction Λ f M (AsSmall.down.obj U).hom)) :
    Nonempty (((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
      ((coefficientModelFixedScalars _ k).obj
        ((smallModules X (condensedRingObj Λ X) ⋙ ConstantCompletion.res c.hom).obj N))).over U ≅
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
        ((coefficientModelFixedScalars _ k).obj
          ((smallModules X (condensedRingObj Λ X) ⋙
            ConstantCompletion.res c.hom).obj M))).over U) := by
  exact slice_of_model_iso Λ f k c N M U
    (model_iso_after_composite Λ f (AsSmall.down.obj U).hom k c N M h)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
