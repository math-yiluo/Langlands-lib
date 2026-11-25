/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

import WeilConjectures.AlgebraicGeometry.HomComplexSingleNaturality
import WeilConjectures.AlgebraicGeometry.UnderivedAffineHomCounit

@[expose] public section
universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace AlgebraicGeometry

private noncomputable def unitHomIso (Y : Scheme.{u}) :
    (SheafOfModules.homFunctor Y.sheaf).obj
      (op (SheafOfModules.unit Y.ringCatSheaf)) ≅
        𝟭 (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  NatIso.ofComponents (fun F ↦ SheafOfModules.homObjUnitIso (R := Y.sheaf) F) (by
    intro F G g
    apply SheafOfModules.hom_ext
    ext U φ
    rfl)

private theorem adjustComparison {C : Type*} [Category C] {K : C ⥤ C}
    (e₀ e : K ≅ 𝟭 C) {A I B : C} (d₀ : A ≅ B) (p : B ⟶ K.obj I) (c : A ⟶ I)
    (hc : d₀.hom ≫ p ≫ e₀.hom.app I = c) :
    ∃ d : A ≅ B, d.hom ≫ p ≫ e.hom.app I = c := by
  let a : 𝟭 C ≅ 𝟭 C := e₀.symm ≪≫ e
  have he : e.hom.app I = e₀.hom.app I ≫ a.hom.app I := by
    change e.hom.app I = e₀.hom.app I ≫ e₀.inv.app I ≫ e.hom.app I
    simp only [Iso.hom_inv_id_app_assoc]
  refine ⟨a.symm.app A ≪≫ d₀, ?_⟩
  change (a.inv.app A ≫ d₀.hom) ≫ p ≫ e.hom.app I = c
  rw [he]
  simp only [Category.assoc]
  rw [← Category.assoc p (e₀.hom.app I) (a.hom.app I),
    ← Category.assoc d₀.hom (p ≫ e₀.hom.app I) (a.hom.app I), hc]
  have hn : c ≫ a.inv.app I = a.inv.app A ≫ c := a.inv.naturality c
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]

private theorem affineHom_mapComparison
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (H : C ⥤ D) (R : D ⥤ C) [H.Additive] [R.Additive]
    {K T : C ⥤ C} [K.Additive] [T.Additive]
    (j : H ⋙ R ≅ K) (t : T ≅ 𝟭 C) (p : K ⟶ T) (c : H ⋙ R ⟶ 𝟭 C)
    (hj : ∀ M, j.hom.app M ≫ p.app M ≫ t.hom.app M = c.app M)
    {F G : CochainComplex C ℤ ⥤ CochainComplex C ℤ}
    (bB : F ≅ K.mapHomologicalComplex (.up ℤ))
    (bO : G ≅ T.mapHomologicalComplex (.up ℤ)) (q : F ⟶ G)
    (hb : ∀ I, q.app I ≫ bO.hom.app I =
      bB.hom.app I ≫ (NatTrans.mapHomologicalComplex p (.up ℤ)).app I)
    (e : G ≅ 𝟭 _) (I : CochainComplex C ℤ) :
    ∃ d : (R.mapHomologicalComplex (.up ℤ)).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj I) ≅ F.obj I,
      d.hom ≫ q.app I ≫ e.hom.app I =
        (NatTrans.mapHomologicalComplex c (.up ℤ)).app I := by
  let e₀ := bO ≪≫ NatIso.mapHomologicalComplex t (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let d₀ := ((Functor.mapHomologicalComplexCompIso j (.up ℤ)).app I) ≪≫
    (bB.app I).symm
  have hc : d₀.hom ≫ q.app I ≫ e₀.hom.app I =
      (NatTrans.mapHomologicalComplex c (.up ℤ)).app I := by
    simp only [d₀, e₀, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      NatTrans.comp_app, Category.assoc]
    rw [← Category.assoc _ (bO.hom.app I) _, hb I]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    apply HomologicalComplex.hom_ext
    intro n
    change j.hom.app (I.X n) ≫ p.app (I.X n) ≫ t.hom.app (I.X n) ≫ 𝟙 _ =
      c.app (I.X n)
    rw [Category.comp_id]
    exact hj (I.X n)
  exact adjustComparison e₀ e d₀ (q.app I)
    ((NatTrans.mapHomologicalComplex c (.up ℤ)).app I) hc

set_option backward.isDefEq.respectTransparency false in
-- Unfold the sheaf carrier encodings in the two comparison isomorphisms.
/-- Degreewise affine Hom comparison data.

This is the termwise part of the chain-map comparison; the chain-map
extensionality argument is supplied by `affine_hom_complex_d`.
Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0, and 0AX3.
(blueprint: lem-sc-affine-hom-complex-evaluation-d-components) -/
theorem affine_hom_complex_d_components
    {Y X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
      [H.Additive]
      (iH : H ⋙ SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor Y.sheaf).obj
          (op ((SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
              (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))
      (adj₀ : SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ⊣ H)
    (h_eval : ∀ (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (U : Y.Opens)
          (φ : (H.obj F).val.obj (op U)),
        ((adj₀.counit.app F).val.app (op U)).hom φ =
          ((((iH.hom.app F).val.app (op U)).hom φ).app (op (Over.mk (𝟙 U)))).hom
            (1 : (moduleRings (directImageAlgebraSpace f)).obj.obj (op U)))
    (e : (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _) :
    ∀ I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      ∃ d : (((SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
            (.up ℤ)).obj ((H.mapHomologicalComplex (.up ℤ)).obj I)) ≅
          homComplex (R := Y.toRingedSpace.sheaf)
            ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                ((Scheme.Modules.pushforward f).obj
                  (SheafOfModules.unit X.ringCatSheaf))) I,
        ∀ n : ℤ, d.hom.f n ≫ (((homComplexFunctor (R := Y.toRingedSpace.sheaf)).map
          (((CochainComplex.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op)).app I).f n ≫
            (e.hom.app I).f n =
            ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app I).f n := by
  classical
  let B := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  let k := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let j : H ⋙ SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor Y.sheaf).obj (op B) := iH
  have hj := underived_affine_hom_counit f H iH adj₀ h_eval
  let instB : ((SheafOfModules.homFunctor Y.sheaf).obj (op B)).Additive :=
    Functor.additive_of_iso j
  let instO : ((SheafOfModules.homFunctor Y.sheaf).obj
      (op (SheafOfModules.unit Y.ringCatSheaf))).Additive :=
    Functor.additive_of_iso (unitHomIso Y).symm
  obtain ⟨bB, bO, hb⟩ := @homComplex_single_precomposition_iso Y B
    (SheafOfModules.unit Y.ringCatSheaf) k instB instO
  intro I
  obtain ⟨d, hd⟩ := affineHom_mapComparison H
    (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩)
    j (unitHomIso Y) ((SheafOfModules.homFunctor Y.sheaf).map k.op)
    adj₀.counit hj bB bO
    ((homComplexFunctor (R := Y.sheaf)).map
      ((CochainComplex.singleFunctor _ 0).map k).op) hb e I
  refine ⟨d, ?_⟩
  intro n
  exact congrArg (fun g ↦ g.f n) hd

/-- (blueprint: lem-sc-affine-hom-complex-evaluation-d) -/
theorem affine_hom_complex_d
    {Y X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
      [H.Additive]
      (iH : H ⋙ SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor Y.sheaf).obj
          (op ((SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
              (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))
      (adj₀ : SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ⊣ H)
    (h_eval : ∀ (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (U : Y.Opens)
          (φ : (H.obj F).val.obj (op U)),
        ((adj₀.counit.app F).val.app (op U)).hom φ =
          ((((iH.hom.app F).val.app (op U)).hom φ).app (op (Over.mk (𝟙 U)))).hom
            (1 : (moduleRings (directImageAlgebraSpace f)).obj.obj (op U)))
    (e : (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _) :
    ∀ I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      ∃ d : (((SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
            (.up ℤ)).obj ((H.mapHomologicalComplex (.up ℤ)).obj I)) ≅
          homComplex (R := Y.toRingedSpace.sheaf)
            ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                ((Scheme.Modules.pushforward f).obj
                  (SheafOfModules.unit X.ringCatSheaf))) I,
        d.hom ≫ ((homComplexFunctor (R := Y.toRingedSpace.sheaf)).map
          (((CochainComplex.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op)).app I ≫
            e.hom.app I =
              ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app I) := by
  intro I
  obtain ⟨d, hd⟩ := affine_hom_complex_d_components f H iH adj₀ h_eval e I
  refine ⟨d, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  exact hd n

end AlgebraicGeometry
