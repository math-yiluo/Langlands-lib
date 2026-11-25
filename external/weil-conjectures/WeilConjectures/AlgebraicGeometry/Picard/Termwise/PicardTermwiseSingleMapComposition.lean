/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardTermwiseModels
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit

/-! # Composition of the canonical termwise single map

## References

* Stacks Project, Tags 06YJ and 0D5S
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

private theorem single_composition
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [HasZeroObject A] [HasZeroObject B] [HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (N : A) :
    (Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app
        ((CochainComplex.singleFunctor A 0).obj N) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app N =
    (G.mapHomologicalComplex (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app N) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj N) ≫
      (CochainComplex.singleFunctor C 0).map (c.hom.app N) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [CochainComplex.singleFunctor,
    HomologicalComplex.singleMapHomologicalComplex,
    HomologicalComplex.single, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
    Functor.mapHomologicalComplex]

private theorem cancel_composition_maps
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : B} {U V : A} (p : X ⟶ Y) (j : Y ≅ F.obj U) (b : U ≅ V) :
    (p ≫ j.hom ≫ F.map b.hom) ≫ F.map b.inv ≫ j.inv = p := by
  simp only [Category.assoc, ← F.map_comp_assoc, b.hom_inv_id, F.map_id,
    Category.id_comp, j.hom_inv_id, Category.comp_id]

private theorem single_composition_restriction
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [HasZeroObject A] [HasZeroObject B] [HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (N : A) :
    (Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app
        ((CochainComplex.singleFunctor A 0).obj N) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app N ≫
      (CochainComplex.singleFunctor C 0).map (c.inv.app N) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app (F.obj N) =
    (G.mapHomologicalComplex (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app N) := by
  have h := congrArg (fun k ↦ k ≫
    (CochainComplex.singleFunctor C 0).map (c.inv.app N) ≫
    (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app (F.obj N))
    (single_composition F G H c N)
  simpa only [Category.assoc] using h.trans
    (cancel_composition_maps (CochainComplex.singleFunctor C 0) _
      ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).app (F.obj N))
      (c.app N))

private theorem cancel_single_maps
    {A C : Type*} [Category A] [Category C]
    (F : A ⥤ C) {X Y : C} {U V : A} (e : X ⟶ Y) (q : Y ⟶ F.obj U) (b : U ≅ V) :
    (e ≫ q ≫ F.map b.hom) ≫ F.map b.inv = e ≫ q := by
  simp only [Category.assoc, ← F.map_comp, b.hom_inv_id, F.map_id, Category.comp_id]

private theorem finish_composition
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {B U V W X : D} {Y Z Z' : C}
    {c : L.obj Y ⟶ B} {e : B ⟶ V} {α : B ⟶ W} {r : V ⟶ W} {u : W ⟶ X}
    {a : Y ⟶ Z} {α' : Y ⟶ Z'} {r' : Z ⟶ Z'}
    {b : L.obj Z ⟶ U} {d : U ⟶ V} {v : U ⟶ X}
    {b' η : L.obj Z' ⟶ X}
    (hα : α = e ≫ r) (hα' : α' = a ≫ r') (hη : η = b')
    (hfac : c ≫ e = L.map a ≫ b ≫ d)
    (hu : d ≫ r ≫ u = v) (hn : L.map r' ≫ b' = b ≫ v) :
    c ≫ α ≫ u = L.map α' ≫ η := by
  rw [hα, hα', hη, ← Category.assoc, ← Category.assoc, hfac]
  simp only [L.map_comp, Category.assoc]
  rw [hu, ← hn]

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- The pinned single pullback map, retaining the tensor-pulled module as its target.
This is a real composite of the derived counit and canonical single comparisons. -/
def picardTermwiseSingleMap {W T : Scheme.{v}} (t : T ⟶ W) (M : W.Modules) :
    (derivedPullback t).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj M) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
          ((Modules.tensorPullback t).obj M)) :=
  Modules.canonicalSinglePullbackMap t M ≫
    (DerivedCategory.singleFunctor _ 0).map
      (((Classical.choose (Modules.exists_tensorPullbackAdjunction t)).leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction t)).inv.app M)

attribute [local irreducible]
  Modules.tensorPullbackCompositionIso Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Modules.Hom DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh

private theorem single_map_normalize {X Y : Scheme.{v}} (f : X ⟶ Y)
    (N : Y.Modules) :
    let := Modules.canonicalTensorPullbackAdditive f
    picardTermwiseSingleMap f N =
      (perfectHomTensorCounit f).app
        ((HomotopyCategory.singleFunctor _ 0).obj N) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Modules.tensorPullback f) (.up ℤ) 0).hom.app N)) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  simp only [picardTermwiseSingleMap, Modules.canonicalSinglePullbackMap, cast_eq,
    Scheme.Modules, Scheme.ringCatSheaf, moduleRings,
    Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id, perfectHomTensorCounit]

private theorem counit_normalize {X Y : Scheme.{v}} (f : X ⟶ Y)
    (K : CochainComplex Y.Modules ℤ) :
    let := Modules.canonicalTensorPullbackAdditive f
    (picardTermwiseCounit f).app K =
      (perfectHomTensorCounit f).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) := by
  have hnorm (A : schemeDerivedCategory Y)
      (B : HomotopyCategory X.Modules (.up ℤ))
      (e : (derivedPullback f).obj A ⟶ DerivedCategory.Qh.obj B) :
      (derivedPullback f).map (𝟙 A) ≫ e ≫ DerivedCategory.Qh.map (𝟙 B) ≫
        𝟙 (DerivedCategory.Qh.obj B) = e := by
    simp
  simp only [picardTermwiseCounit, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  exact hnorm _ _ _

attribute [local irreducible] picardTermwiseCounit picardTermwiseSingleMap
  Modules.canonicalSinglePullbackMap

-- Retain shared local comparison data instead of traversing its choice specifications again.
set_option cleanup.letToHave false in
-- The pinned counit and composition choices have large dependent types.
/-- The canonical maps on arbitrary singles satisfy the composition counit equation.
No flatness, invertibility, or choice of a comparison family is asserted here. -/
theorem picardTermwiseSingleMap_composition
    {W T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
    (ht : i ≫ t = t') (M : W.Modules) :
    let : (Modules.tensorPullback i).Additive :=
      (Classical.choose (Modules.exists_tensorPullbackAdjunction i)).left_adjoint_additive
    let u := (CochainComplex.singleFunctor
      (SheafOfModules.{v} (moduleRings T'.toRingedSpace)) 0).mapIso
        ((Modules.tensorPullbackCompositionIso i t t' ht).app M) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (Modules.tensorPullback i) (.up ℤ) 0).app ((Modules.tensorPullback t).obj M)).symm
    let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
        eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
    c.hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj M) ≫
        picardTermwiseSingleMap t' M ≫ DerivedCategory.Q.map u.hom =
      (derivedPullback i).map (picardTermwiseSingleMap t M) ≫
        (picardTermwiseCounit i).app ((CochainComplex.singleFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 0).obj
            ((Modules.tensorPullback t).obj M)) := by
  subst t'
  simp only [eqToIso_refl, Iso.trans_refl]
  let := perfectHomTensorAdditive i
  let := perfectHomTensorAdditive t
  let := perfectHomTensorAdditive (i ≫ t)
  let P := (CochainComplex.singleFunctor W.Modules 0).obj M
  let q := (HomotopyCategory.quotient W.Modules (.up ℤ)).obj P
  let δ := perfectHomTensorComp i t
  let d := perfectHomTensorHomotopyComp i t
  have fac := perfectHomTensorCounit_comp i t q
  let b := Modules.tensorPullbackCompositionIso i t (i ≫ t) rfl
  let r_t := (HomologicalComplex.singleMapHomologicalComplex
    (Modules.tensorPullback t) (.up ℤ) 0).hom.app M
  let r_it := (HomologicalComplex.singleMapHomologicalComplex
    (Modules.tensorPullback (i ≫ t)) (.up ℤ) 0).hom.app M
  let r_i := (HomologicalComplex.singleMapHomologicalComplex
    (Modules.tensorPullback i) (.up ℤ) 0).app ((Modules.tensorPullback t).obj M)
  let u := (CochainComplex.singleFunctor T'.Modules 0).mapIso (b.app M) ≪≫ r_i.symm
  let D := (perfectHomTensorComplexComp i t).hom.app P
  have htensor : b.inv = δ.hom := by
    dsimp only [b, δ, perfectHomTensorComp]
    unfold Modules.tensorPullbackCompositionIso
    have hpush : Modules.pushforwardCongr (rfl : (i ≫ t) = (i ≫ t)) =
        Iso.refl _ := by
      ext M U
      simp
    rw [hpush]
    simp only [Iso.trans_refl, conjugateIsoEquiv_symm_apply_inv,
      conjugateIsoEquiv_symm_apply_hom, Iso.symm_hom]
  have hb : δ.hom = b.inv := htensor.symm
  have hb' : δ = b.symm := Iso.ext hb
  have hb_inv : δ.inv = b.hom := congrArg Iso.inv hb'
  have hs : D ≫ r_it ≫ u.hom =
      ((Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).map r_t := by
    have h := single_composition_restriction (Modules.tensorPullback t)
      (Modules.tensorPullback i) (Modules.tensorPullback (i ≫ t)) δ M
    simpa only [D, perfectHomTensorComplexComp, hb_inv, u, r_i, Iso.trans_hom,
      Functor.mapIso_hom,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc] using h
  have hd : d.hom.app q = (HomotopyCategory.quotient T'.Modules (.up ℤ)).map D :=
    perfectHomTensorHomotopyComp_hom_app i t P
  have hsq : DerivedCategory.Qh.map (d.hom.app q) ≫
      DerivedCategory.Q.map r_it ≫ DerivedCategory.Q.map u.hom =
    DerivedCategory.Qh.map (((Modules.tensorPullback i).mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient T.Modules (.up ℤ)).map r_t)) := by
    rw [hd]
    change DerivedCategory.Q.map D ≫ DerivedCategory.Q.map r_it ≫
      DerivedCategory.Q.map u.hom = DerivedCategory.Q.map _
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ DerivedCategory.Q.map k) hs
  have hn := (perfectHomTensorCounit i).naturality
    ((HomotopyCategory.quotient T.Modules (.up ℤ)).map r_t)
  change (derivedPullback i).map (DerivedCategory.Q.map r_t) ≫
      (perfectHomTensorCounit i).app ((HomotopyCategory.singleFunctor T.Modules 0).obj
        ((Modules.tensorPullback t).obj M)) =
    (perfectHomTensorCounit i).app
      (((Modules.tensorPullback t).mapHomotopyCategory (.up ℤ)).obj q) ≫
      DerivedCategory.Qh.map (((Modules.tensorPullback i).mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient T.Modules (.up ℤ)).map r_t)) at hn
  exact finish_composition (derivedPullback i)
    (single_map_normalize (i ≫ t) M) (single_map_normalize t M)
    (counit_normalize i ((CochainComplex.singleFunctor T.Modules 0).obj
      ((Modules.tensorPullback t).obj M))) fac hsq hn

end
end AlgebraicGeometry.Scheme
