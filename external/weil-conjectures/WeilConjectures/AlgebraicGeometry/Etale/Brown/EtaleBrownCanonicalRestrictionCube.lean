/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownCanonicalRestriction
public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownInverseRepresentative
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownImageRealizationDerived
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import WeilConjectures.CategoryTheory.Adjunction.MateCube

/-! # The canonical restriction model in geometric scalar coordinates

Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks 07A4 and 0FND.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

private theorem inverse_face
    {C : Type*} [Category C] {A B C' D : C}
    (i : A ≅ B) (j : C' ≅ D) (f : A ⟶ C') (g : B ⟶ D)
    (h : i.hom ≫ g = f ≫ j.hom) : i.inv ≫ f = g ≫ j.inv := by
  apply (cancel_epi i.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem brown_cube_reorient
    {C : Type*} {D : Type*} {E : Type*} {F : Type*}
    {G : Type*} {H : Type*} {I : Type*} {J : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category G] [Category H] [Category I] [Category J]
    {a : C ⥤ D} {b : D ⥤ E} {c : E ⥤ F} {d : C ⥤ G}
    {e : G ⥤ E} {f : G ⥤ H} {g : H ⥤ F} {h : C ⥤ I}
    {i : I ⥤ H} {j : D ⥤ J} {k : J ⥤ F} {m : I ⥤ J}
    (s1 : a ⋙ b ≅ d ⋙ e) (s2 : e ⋙ c ≅ f ⋙ g)
    (s3 : d ⋙ f ≅ h ⋙ i) (s4 : b ⋙ c ≅ j ⋙ k)
    (s5 : a ⋙ j ≅ h ⋙ m) (s6 : m ⋙ k ≅ i ⋙ g)
    (comm : whiskerRight s1.hom c ≫ whiskerLeft d s2.hom ≫ whiskerRight s3.hom g =
      whiskerLeft a s4.hom ≫ whiskerRight s5.hom k ≫ whiskerLeft h s6.hom) :
    ∀ X, k.map (s5.hom.app X) ≫ s6.hom.app (h.obj X) ≫ g.map (s3.inv.app X) =
      s4.inv.app (a.obj X) ≫ c.map (s1.hom.app X) ≫ s2.hom.app (d.obj X) := by
  have hh := inverse_face (isoWhiskerLeft a s4) (isoWhiskerRight s3 g)
    (whiskerRight s1.hom c ≫ whiskerLeft d s2.hom)
    (whiskerRight s5.hom k ≫ whiskerLeft h s6.hom)
    (by simpa only [isoWhiskerLeft_hom, isoWhiskerRight_hom, Category.assoc]
      using comm.symm)
  intro X
  have hx := congrArg (fun z ↦ z.app X) hh.symm
  simpa only [NatTrans.comp_app, isoWhiskerLeft_inv, isoWhiskerRight_inv,
    whiskerLeft_app, whiskerRight_app, Category.assoc] using hx

section NormalizedCube
variable {C Cd : Type*} [Category C] [Category Cd]
variable {D Dd : Type*} [Category D] [Category Dd]
variable {E Ed : Type*} [Category E] [Category Ed]
variable {F Fd : Type*} [Category F] [Category Fd]
variable {G Gd : Type*} [Category G] [Category Gd]
variable {H Hd : Type*} [Category H] [Category Hd]
variable {I Id : Type*} [Category I] [Category Id]
variable {J Jd : Type*} [Category J] [Category Jd]

private theorem brown_normalized_cube_hom
    (QC : C ⥤ Cd) [QC.EssSurj]
    (QD : D ⥤ Dd)
    (QE : E ⥤ Ed)
    (QF : F ⥤ Fd)
    (QG : G ⥤ Gd)
    (QH : H ⥤ Hd)
    (QI : I ⥤ Id)
    (QJ : J ⥤ Jd)
    (a : C ⥤ D) (aD : Cd ⥤ Dd)
    (b : D ⥤ E) (bD : Dd ⥤ Ed)
    (c : E ⥤ F) (cD : Ed ⥤ Fd)
    (d : C ⥤ G) (dD : Cd ⥤ Gd)
    (e : G ⥤ E) (eD : Gd ⥤ Ed)
    (f : G ⥤ H) (fD : Gd ⥤ Hd)
    (g : H ⥤ F) (gD : Hd ⥤ Fd)
    (h : C ⥤ I) (hD : Cd ⥤ Id)
    (i : I ⥤ H) (iD : Id ⥤ Hd)
    (j : D ⥤ J) (jD : Dd ⥤ Jd)
    (k : J ⥤ F) (kD : Jd ⥤ Fd)
    (m : I ⥤ J) (mD : Id ⥤ Jd)
    (φa : QC ⋙ aD ≅ a ⋙ QD)
    (φb : QD ⋙ bD ≅ b ⋙ QE)
    (φc : QE ⋙ cD ≅ c ⋙ QF)
    (φd : QC ⋙ dD ≅ d ⋙ QG)
    (φe : QG ⋙ eD ≅ e ⋙ QE)
    (φf : QG ⋙ fD ≅ f ⋙ QH)
    (φg : QH ⋙ gD ≅ g ⋙ QF)
    (φh : QC ⋙ hD ≅ h ⋙ QI)
    (φi : QI ⋙ iD ≅ i ⋙ QH)
    (φj : QD ⋙ jD ≅ j ⋙ QJ)
    (φk : QJ ⋙ kD ≅ k ⋙ QF)
    (φm : QI ⋙ mD ≅ m ⋙ QJ)
    (q1 : a ⋙ b ≅ d ⋙ e)
    (s1 : aD ⋙ bD ≅ dD ⋙ eD)
    (h1 : ∀ X, s1.hom.app (QC.obj X) ≫
      eD.map (φd.hom.app X) ≫ φe.hom.app (d.obj X) =
      bD.map (φa.hom.app X) ≫ φb.hom.app (a.obj X) ≫
        QE.map (q1.hom.app X))
    (q2 : e ⋙ c ≅ f ⋙ g)
    (s2 : eD ⋙ cD ≅ fD ⋙ gD)
    (h2 : ∀ X, s2.hom.app (QG.obj X) ≫
      gD.map (φf.hom.app X) ≫ φg.hom.app (f.obj X) =
      cD.map (φe.hom.app X) ≫ φc.hom.app (e.obj X) ≫
        QF.map (q2.hom.app X))
    (q3 : d ⋙ f ≅ h ⋙ i)
    (s3 : dD ⋙ fD ≅ hD ⋙ iD)
    (h3 : ∀ X, s3.hom.app (QC.obj X) ≫
      iD.map (φh.hom.app X) ≫ φi.hom.app (h.obj X) =
      fD.map (φd.hom.app X) ≫ φf.hom.app (d.obj X) ≫
        QH.map (q3.hom.app X))
    (q4 : b ⋙ c ≅ j ⋙ k)
    (s4 : bD ⋙ cD ≅ jD ⋙ kD)
    (h4 : ∀ X, s4.hom.app (QD.obj X) ≫
      kD.map (φj.hom.app X) ≫ φk.hom.app (j.obj X) =
      cD.map (φb.hom.app X) ≫ φc.hom.app (b.obj X) ≫
        QF.map (q4.hom.app X))
    (q5 : a ⋙ j ≅ h ⋙ m)
    (s5 : aD ⋙ jD ≅ hD ⋙ mD)
    (h5 : ∀ X, s5.hom.app (QC.obj X) ≫
      mD.map (φh.hom.app X) ≫ φm.hom.app (h.obj X) =
      jD.map (φa.hom.app X) ≫ φj.hom.app (a.obj X) ≫
        QJ.map (q5.hom.app X))
    (q6 : m ⋙ k ≅ i ⋙ g)
    (s6 : mD ⋙ kD ≅ iD ⋙ gD)
    (h6 : ∀ X, s6.hom.app (QI.obj X) ≫
      gD.map (φi.hom.app X) ≫ φg.hom.app (i.obj X) =
      kD.map (φm.hom.app X) ≫ φk.hom.app (m.obj X) ≫
        QF.map (q6.hom.app X))
    (comm : ∀ X, c.map (q1.hom.app X) ≫ q2.hom.app (d.obj X) ≫
      g.map (q3.hom.app X) = q4.hom.app (a.obj X) ≫
        k.map (q5.hom.app X) ≫ q6.hom.app (h.obj X)) :
    ∀ X, kD.map (s5.hom.app X) ≫ s6.hom.app (hD.obj X) ≫ gD.map (s3.inv.app X) =
      s4.inv.app (aD.obj X) ≫ cD.map (s1.hom.app X) ≫ s2.hom.app (dD.obj X) := by
  apply brown_cube_reorient
    (a := aD) (b := bD) (c := cD) (d := dD) (e := eD) (f := fD)
    (g := gD) (h := hD) (i := iD) (j := jD) (k := kD) (m := mD)
    s1 s2 s3 s4 s5 s6
  let α := whiskerRight s1.hom cD ≫ whiskerLeft dD s2.hom ≫ whiskerRight s3.hom gD
  let β := whiskerLeft aD s4.hom ≫ whiskerRight s5.hom kD ≫ whiskerLeft hD s6.hom
  change α = β
  suffices hh : ∀ X, α.app (QC.obj X) = β.app (QC.obj X) by
    ext N
    let eX := QC.objObjPreimageIso N
    apply (cancel_mono ((hD ⋙ iD ⋙ gD).map eX.inv)).mp
    have ha := α.naturality eX.inv
    have hb := β.naturality eX.inv
    dsimp only [Functor.comp_map] at ha hb ⊢
    rw [← ha, ← hb, hh]
  intro X
  dsimp only [α, β]
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  apply (cancel_mono
    (gD.map (iD.map (φh.hom.app X)) ≫
      gD.map (φi.hom.app (h.obj X)) ≫ φg.hom.app (i.obj (h.obj X)))).mp
  have n2 := s2.hom.naturality (φd.hom.app X)
  have n4 := s4.hom.naturality (φa.hom.app X)
  have n6 := s6.hom.naturality (φh.hom.app X)
  dsimp only [Functor.comp_map] at n2 n4 n6
  have nl : cD.map (s1.hom.app (QC.obj X)) ≫
      s2.hom.app (dD.obj (QC.obj X)) ≫ gD.map (s3.hom.app (QC.obj X)) ≫
      gD.map (iD.map (φh.hom.app X)) ≫
      gD.map (φi.hom.app (h.obj X)) ≫ φg.hom.app (i.obj (h.obj X)) =
    cD.map (bD.map (φa.hom.app X)) ≫
      cD.map (φb.hom.app (a.obj X)) ≫ φc.hom.app (b.obj (a.obj X)) ≫
      QF.map (c.map (q1.hom.app X) ≫ q2.hom.app (d.obj X) ≫
        g.map (q3.hom.app X)) := by
    erw [← gD.map_comp_assoc, ← gD.map_comp_assoc]
    simp only [Category.assoc]
    erw [h3]
    simp only [Functor.map_comp, Category.assoc]
    erw [φg.hom.naturality]
    erw [← reassoc_of% n2, reassoc_of% h2]
    erw [← cD.map_comp_assoc, ← cD.map_comp_assoc]
    simp only [Category.assoc]
    erw [h1]
    simp only [Functor.map_comp, Category.assoc]
    erw [φc.hom.naturality_assoc]
    simp only [Functor.comp_map]
  simp only [Category.assoc]
  erw [nl]
  erw [← reassoc_of% n6]
  erw [h6]
  erw [← kD.map_comp_assoc, ← kD.map_comp_assoc]
  simp only [Category.assoc]
  erw [h5]
  simp only [Functor.map_comp, Category.assoc]
  erw [φk.hom.naturality_assoc]
  erw [← reassoc_of% n4, reassoc_of% h4]
  simp only [Functor.comp_map, ← Functor.map_comp]
  repeat' apply congrArg (fun t ↦ _ ≫ t)
  exact congrArg QF.map (comm X)

end NormalizedCube

section BrownCochainCube

private theorem brown_cochain_preservesZeroMorphisms_comp
    {C : Type*} {D : Type*} {E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (F : C ⥤ D) (G : D ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    (F ⋙ G).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_comp _ _

attribute [local instance] brown_cochain_preservesZeroMorphisms_comp

private theorem brown_cochain_cube
    {C : Type*} {D : Type*} {E : Type*} {F : Type*}
    {G : Type*} {H : Type*} {I : Type*} {J : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category G] [Category H] [Category I] [Category J]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E] [HasZeroMorphisms F]
    [HasZeroMorphisms G] [HasZeroMorphisms H] [HasZeroMorphisms I] [HasZeroMorphisms J]
    {a : C ⥤ D} {b : D ⥤ E} {c : E ⥤ F} {d : C ⥤ G}
    {e : G ⥤ E} {f : G ⥤ H} {g : H ⥤ F} {h : C ⥤ I}
    {i : I ⥤ H} {j : D ⥤ J} {k : J ⥤ F} {m : I ⥤ J}
    [a.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    [c.PreservesZeroMorphisms] [d.PreservesZeroMorphisms]
    [e.PreservesZeroMorphisms] [f.PreservesZeroMorphisms]
    [g.PreservesZeroMorphisms] [h.PreservesZeroMorphisms]
    [i.PreservesZeroMorphisms] [j.PreservesZeroMorphisms]
    [k.PreservesZeroMorphisms] [m.PreservesZeroMorphisms]
    (q1 : a ⋙ b ≅ d ⋙ e) (q2 : e ⋙ c ≅ f ⋙ g)
    (q3 : d ⋙ f ≅ h ⋙ i) (q4 : b ⋙ c ≅ j ⋙ k)
    (q5 : a ⋙ j ≅ h ⋙ m) (q6 : m ⋙ k ≅ i ⋙ g)
    (comm : ∀ X, c.map (q1.hom.app X) ≫ q2.hom.app (d.obj X) ≫
      g.map (q3.hom.app X) = q4.hom.app (a.obj X) ≫
        k.map (q5.hom.app X) ≫ q6.hom.app (h.obj X)) :
    ∀ K : CochainComplex C ℤ,
      (c.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex q1 (.up ℤ)).hom.app K) ≫
        (NatIso.mapHomologicalComplex q2 (.up ℤ)).hom.app
          ((d.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (g.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex q3 (.up ℤ)).hom.app K) =
      (NatIso.mapHomologicalComplex q4 (.up ℤ)).hom.app
          ((a.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (k.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex q5 (.up ℤ)).hom.app K) ≫
        (NatIso.mapHomologicalComplex q6 (.up ℤ)).hom.app
          ((h.mapHomologicalComplex (.up ℤ)).obj K) := by
  intro K
  apply HomologicalComplex.hom_ext
  intro n
  simpa only [HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f]
    using comm (K.X n)

end BrownCochainCube

section CochainNormalizedCube
variable {C Cd : Type*} [Category C] [Category Cd]
variable {D Dd : Type*} [Category D] [Category Dd]
variable {E Ed : Type*} [Category E] [Category Ed]
variable {F Fd : Type*} [Category F] [Category Fd]
variable {G Gd : Type*} [Category G] [Category Gd]
variable {H Hd : Type*} [Category H] [Category Hd]
variable {I Id : Type*} [Category I] [Category Id]
variable {J Jd : Type*} [Category J] [Category Jd]

attribute [local instance] brown_cochain_preservesZeroMorphisms_comp
variable [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  [HasZeroMorphisms F] [HasZeroMorphisms G] [HasZeroMorphisms H]
  [HasZeroMorphisms I] [HasZeroMorphisms J]

private theorem brown_cochain_normalized_cube
    (QC : CochainComplex C ℤ ⥤ Cd) [QC.EssSurj]
    (QD : CochainComplex D ℤ ⥤ Dd)
    (QE : CochainComplex E ℤ ⥤ Ed)
    (QF : CochainComplex F ℤ ⥤ Fd)
    (QG : CochainComplex G ℤ ⥤ Gd)
    (QH : CochainComplex H ℤ ⥤ Hd)
    (QI : CochainComplex I ℤ ⥤ Id)
    (QJ : CochainComplex J ℤ ⥤ Jd)
    (a : C ⥤ D) (aD : Cd ⥤ Dd)
    (b : D ⥤ E) (bD : Dd ⥤ Ed)
    (c : E ⥤ F) (cD : Ed ⥤ Fd)
    (d : C ⥤ G) (dD : Cd ⥤ Gd)
    (e : G ⥤ E) (eD : Gd ⥤ Ed)
    (f : G ⥤ H) (fD : Gd ⥤ Hd)
    (g : H ⥤ F) (gD : Hd ⥤ Fd)
    (h : C ⥤ I) (hD : Cd ⥤ Id)
    (i : I ⥤ H) (iD : Id ⥤ Hd)
    (j : D ⥤ J) (jD : Dd ⥤ Jd)
    (k : J ⥤ F) (kD : Jd ⥤ Fd)
    (m : I ⥤ J) (mD : Id ⥤ Jd)
    [a.PreservesZeroMorphisms]
    [b.PreservesZeroMorphisms]
    [c.PreservesZeroMorphisms]
    [d.PreservesZeroMorphisms]
    [e.PreservesZeroMorphisms]
    [f.PreservesZeroMorphisms]
    [g.PreservesZeroMorphisms]
    [h.PreservesZeroMorphisms]
    [i.PreservesZeroMorphisms]
    [j.PreservesZeroMorphisms]
    [k.PreservesZeroMorphisms]
    [m.PreservesZeroMorphisms]
    (φa : QC ⋙ aD ≅ (a.mapHomologicalComplex (.up ℤ)) ⋙ QD)
    (φb : QD ⋙ bD ≅ (b.mapHomologicalComplex (.up ℤ)) ⋙ QE)
    (φc : QE ⋙ cD ≅ (c.mapHomologicalComplex (.up ℤ)) ⋙ QF)
    (φd : QC ⋙ dD ≅ (d.mapHomologicalComplex (.up ℤ)) ⋙ QG)
    (φe : QG ⋙ eD ≅ (e.mapHomologicalComplex (.up ℤ)) ⋙ QE)
    (φf : QG ⋙ fD ≅ (f.mapHomologicalComplex (.up ℤ)) ⋙ QH)
    (φg : QH ⋙ gD ≅ (g.mapHomologicalComplex (.up ℤ)) ⋙ QF)
    (φh : QC ⋙ hD ≅ (h.mapHomologicalComplex (.up ℤ)) ⋙ QI)
    (φi : QI ⋙ iD ≅ (i.mapHomologicalComplex (.up ℤ)) ⋙ QH)
    (φj : QD ⋙ jD ≅ (j.mapHomologicalComplex (.up ℤ)) ⋙ QJ)
    (φk : QJ ⋙ kD ≅ (k.mapHomologicalComplex (.up ℤ)) ⋙ QF)
    (φm : QI ⋙ mD ≅ (m.mapHomologicalComplex (.up ℤ)) ⋙ QJ)
    (q1 : a ⋙ b ≅ d ⋙ e)
    (s1 : aD ⋙ bD ≅ dD ⋙ eD)
    (h1 : ∀ X, s1.hom.app (QC.obj X) ≫
      eD.map (φd.hom.app X) ≫ φe.hom.app ((d.mapHomologicalComplex (.up ℤ)).obj X) =
      bD.map (φa.hom.app X) ≫ φb.hom.app ((a.mapHomologicalComplex (.up ℤ)).obj X) ≫
        QE.map ((NatIso.mapHomologicalComplex q1 (.up ℤ)).hom.app X))
    (q2 : e ⋙ c ≅ f ⋙ g)
    (s2 : eD ⋙ cD ≅ fD ⋙ gD)
    (h2 : ∀ X, s2.hom.app (QG.obj X) ≫
      gD.map (φf.hom.app X) ≫ φg.hom.app ((f.mapHomologicalComplex (.up ℤ)).obj X) =
      cD.map (φe.hom.app X) ≫ φc.hom.app ((e.mapHomologicalComplex (.up ℤ)).obj X) ≫
        QF.map ((NatIso.mapHomologicalComplex q2 (.up ℤ)).hom.app X))
    (q3 : d ⋙ f ≅ h ⋙ i)
    (s3 : dD ⋙ fD ≅ hD ⋙ iD)
    (h3 : ∀ X, s3.hom.app (QC.obj X) ≫
      iD.map (φh.hom.app X) ≫ φi.hom.app ((h.mapHomologicalComplex (.up ℤ)).obj X) =
      fD.map (φd.hom.app X) ≫ φf.hom.app ((d.mapHomologicalComplex (.up ℤ)).obj X) ≫
        QH.map ((NatIso.mapHomologicalComplex q3 (.up ℤ)).hom.app X))
    (q4 : b ⋙ c ≅ j ⋙ k)
    (s4 : bD ⋙ cD ≅ jD ⋙ kD)
    (h4 : ∀ X, s4.hom.app (QD.obj X) ≫
      kD.map (φj.hom.app X) ≫ φk.hom.app ((j.mapHomologicalComplex (.up ℤ)).obj X) =
      cD.map (φb.hom.app X) ≫ φc.hom.app ((b.mapHomologicalComplex (.up ℤ)).obj X) ≫
        QF.map ((NatIso.mapHomologicalComplex q4 (.up ℤ)).hom.app X))
    (q5 : a ⋙ j ≅ h ⋙ m)
    (s5 : aD ⋙ jD ≅ hD ⋙ mD)
    (h5 : ∀ X, s5.hom.app (QC.obj X) ≫
      mD.map (φh.hom.app X) ≫ φm.hom.app ((h.mapHomologicalComplex (.up ℤ)).obj X) =
      jD.map (φa.hom.app X) ≫ φj.hom.app ((a.mapHomologicalComplex (.up ℤ)).obj X) ≫
        QJ.map ((NatIso.mapHomologicalComplex q5 (.up ℤ)).hom.app X))
    (q6 : m ⋙ k ≅ i ⋙ g)
    (s6 : mD ⋙ kD ≅ iD ⋙ gD)
    (h6 : ∀ X, s6.hom.app (QI.obj X) ≫
      gD.map (φi.hom.app X) ≫ φg.hom.app ((i.mapHomologicalComplex (.up ℤ)).obj X) =
      kD.map (φm.hom.app X) ≫ φk.hom.app ((m.mapHomologicalComplex (.up ℤ)).obj X) ≫
        QF.map ((NatIso.mapHomologicalComplex q6 (.up ℤ)).hom.app X))
    (comm : ∀ X, c.map (q1.hom.app X) ≫ q2.hom.app (d.obj X) ≫
      g.map (q3.hom.app X) = q4.hom.app (a.obj X) ≫
        k.map (q5.hom.app X) ≫ q6.hom.app (h.obj X)) :
    ∀ X, kD.map (s5.hom.app X) ≫ s6.hom.app (hD.obj X) ≫ gD.map (s3.inv.app X) =
      s4.inv.app (aD.obj X) ≫ cD.map (s1.hom.app X) ≫ s2.hom.app (dD.obj X) := by
  exact brown_normalized_cube_hom
    (QC := QC) (QD := QD) (QE := QE) (QF := QF)
    (QG := QG) (QH := QH) (QI := QI) (QJ := QJ)
    (a := a.mapHomologicalComplex (.up ℤ)) (aD := aD)
    (b := b.mapHomologicalComplex (.up ℤ)) (bD := bD)
    (c := c.mapHomologicalComplex (.up ℤ)) (cD := cD)
    (d := d.mapHomologicalComplex (.up ℤ)) (dD := dD)
    (e := e.mapHomologicalComplex (.up ℤ)) (eD := eD)
    (f := f.mapHomologicalComplex (.up ℤ)) (fD := fD)
    (g := g.mapHomologicalComplex (.up ℤ)) (gD := gD)
    (h := h.mapHomologicalComplex (.up ℤ)) (hD := hD)
    (i := i.mapHomologicalComplex (.up ℤ)) (iD := iD)
    (j := j.mapHomologicalComplex (.up ℤ)) (jD := jD)
    (k := k.mapHomologicalComplex (.up ℤ)) (kD := kD)
    (m := m.mapHomologicalComplex (.up ℤ)) (mD := mD)
    (φa := φa)
    (φb := φb)
    (φc := φc)
    (φd := φd)
    (φe := φe)
    (φf := φf)
    (φg := φg)
    (φh := φh)
    (φi := φi)
    (φj := φj)
    (φk := φk)
    (φm := φm)
    (q1 := NatIso.mapHomologicalComplex q1 (.up ℤ)) (s1 := s1) (h1 := h1)
    (q2 := NatIso.mapHomologicalComplex q2 (.up ℤ)) (s2 := s2) (h2 := h2)
    (q3 := NatIso.mapHomologicalComplex q3 (.up ℤ)) (s3 := s3) (h3 := h3)
    (q4 := NatIso.mapHomologicalComplex q4 (.up ℤ)) (s4 := s4) (h4 := h4)
    (q5 := NatIso.mapHomologicalComplex q5 (.up ℤ)) (s5 := s5) (h5 := h5)
    (q6 := NatIso.mapHomologicalComplex q6 (.up ℤ)) (s6 := s6) (h6 := h6)
    (comm := brown_cochain_cube q1 q2 q3 q4 q5 q6 comm)

end CochainNormalizedCube

section BrownOrdinaryRestriction

universe a₀v a₁v b₀v b₁v xv yv a₀u a₁u b₀u b₁u xu yu
variable {A₀ : Type a₀u} [Category.{a₀v} A₀] {A₁ : Type a₁u} [Category.{a₁v} A₁]
  {B₀ : Type b₀u} [Category.{b₀v} B₀] {B₁ : Type b₁u} [Category.{b₁v} B₁]
  {X : Type xu} [Category.{xv} X] {Y : Type yu} [Category.{yv} Y]
  (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ A₀) (a₀ : F₀ ⊣ G₀)
  (F₁ : A₁ ⥤ B₁) (G₁ : B₁ ⥤ A₁) (a₁ : F₁ ⊣ G₁)
  (RA : A₀ ⥤ A₁) (RB : B₀ ⥤ B₁)
  (Ua : A₁ ⥤ X) (Un : A₀ ⥤ X) (Ub : B₁ ⥤ Y) (Uq : B₀ ⥤ Y)
  (L : X ⥤ Y) (V : Y ⥤ X) (adj : L ⊣ V)
  (ra : RA ⋙ Ua ≅ Un) (rb : RB ⋙ Ub ≅ Uq)
  (mu₀ : F₀ ⋙ Uq ≅ Un ⋙ L) (mu₁ : F₁ ⋙ Ub ≅ Ua ⋙ L)
  (γ₀ : G₀ ⋙ Un ≅ Uq ⋙ V) (γ₁ : G₁ ⋙ Ua ≅ Ub ⋙ V)
  (β : RA ⋙ F₁ ≅ F₀ ⋙ RB)
  (h₀ : ∀ M N (f : F₀.obj M ⟶ N),
    Un.map (a₀.homEquiv M N f) ≫ γ₀.hom.app N =
      adj.homEquiv _ _ (mu₀.inv.app M ≫ Uq.map f))
  (h₁ : ∀ M N (f : F₁.obj M ⟶ N),
    Ua.map (a₁.homEquiv M N f) ≫ γ₁.hom.app N =
      adj.homEquiv _ _ (mu₁.inv.app M ≫ Ub.map f))
  (hβ : ∀ M, Ub.map (β.hom.app M) ≫ rb.hom.app (F₀.obj M) ≫ mu₀.hom.app M =
    mu₁.hom.app (RA.obj M) ≫ L.map (ra.hom.app M))

include h₀ h₁ hβ in
private theorem brownRestrictionMate_underlying (N : B₀) :
    Ua.map ((mateEquiv a₀ a₁ (.mk _ _ _ _ β.hom)).app N) ≫
      γ₁.hom.app (RB.obj N) ≫ V.map (rb.hom.app N) =
        ra.hom.app (G₀.obj N) ≫ γ₀.hom.app N := by
  let α := (mateEquiv a₀ a₁ (.mk _ _ _ _ β.hom))
  let M := G₀.obj N
  let ε := a₀.counit.app N
  have ha : α.app N = a₁.homEquiv _ _
      (β.hom.app M ≫ RB.map ε) := by
    dsimp only [α, mateEquiv, TwoSquare.mk,
      Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
      Functor.leftUnitor_hom_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.comp_obj]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.id_comp]
    dsimp only [Functor.comp_map]
    erw [Category.comp_id]
  rw [ha]
  erw [← Category.assoc, h₁]
  rw [← adj.homEquiv_naturality_right]
  apply (adj.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  have hb := rb.hom.naturality ε
  change Ub.map (RB.map ε) ≫ rb.hom.app N =
    rb.hom.app (F₀.obj M) ≫ Uq.map ε at hb
  simp only [Functor.map_comp, Category.assoc]
  rw [hb]
  have hi := hβ M
  have hi' : mu₁.inv.app (RA.obj M) ≫
      Ub.map (β.hom.app M) ≫
      rb.hom.app (F₀.obj M) =
    L.map (ra.hom.app M) ≫ mu₀.inv.app M := by
    apply (cancel_epi (mu₁.hom.app (RA.obj M))).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    apply (cancel_mono (mu₀.hom.app M)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hi
  dsimp only [Functor.comp_obj]
  slice_lhs 1 3 => exact hi'
  rw [Category.assoc]
  rw [Adjunction.homEquiv_naturality_left_symm]
  have hε : a₀.homEquiv M N ε = 𝟙 M := by
    rw [Adjunction.homEquiv_unit, a₀.right_triangle_components]
  have hn := h₀ M N ε
  rw [hε] at hn
  erw [Un.map_id M, Category.id_comp] at hn
  erw [hn, Equiv.symm_apply_apply]
end BrownOrdinaryRestriction

private theorem brown_transport_cube
    {Wm Wn Vm Vn : Type*}
    [Category Wm] [Category Wn] [Category Vm] [Category Vn]
    (rW : Wm ⥤ Wn) (rV : Vm ⥤ Vn)
    {Fn Ln : Wn ⥤ Vn} {Fm Lm : Wm ⥤ Vm}
    (εn : Ln ≅ Fn) (εm : Lm ≅ Fm) (τ : rW ⋙ Fn ≅ Fm ⋙ rV)
    {A : Wn} {B : Wm} {C : Vn} {D : Vm}
    (qn : Fn.obj A ≅ C) (qm : Fm.obj B ≅ D)
    (a : A ⟶ rW.obj B) (b : C ⟶ rV.obj D)
    (comm : Fn.map a ≫ τ.hom.app B ≫ rV.map qm.hom = qn.hom ≫ b) :
    εn.hom.app A ≫ qn.hom ≫ b =
      Ln.map a ≫ (isoWhiskerLeft rW εn ≪≫ τ ≪≫ isoWhiskerRight εm.symm rV).hom.app B ≫
        rV.map (εm.hom.app B ≫ qm.hom) := by
  rw [← comm]
  dsimp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← εn.hom.naturality_assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app_assoc]

section InverseCube
variable {C₀ C₁ D₀ D₁ E₀ E₁ H₀ H₁ : Type*}
  [Category C₀] [Category C₁] [Category D₀] [Category D₁]
  [Category E₀] [Category E₁] [Category H₀] [Category H₁]
  {F₀ : C₀ ⥤ D₀} {G₀ : D₀ ⥤ C₀} {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁}
  {L₀ : E₀ ⥤ H₀} {R₀ : H₀ ⥤ E₀} {L₁ : E₁ ⥤ H₁} {R₁ : H₁ ⥤ E₁}

private theorem brown_inverse_cube
    (a₀ : F₀ ⊣ G₀) (a₁ : F₁ ⊣ G₁) (b₀ : L₀ ⊣ R₀) (b₁ : L₁ ⊣ R₁)
    {RA : C₀ ⥤ C₁} {RB : D₀ ⥤ D₁} {SA : E₀ ⥤ E₁} {SB : H₀ ⥤ H₁}
    {U₀ : C₀ ⥤ E₀} {V₀ : D₀ ⥤ H₀} {U₁ : C₁ ⥤ E₁} {V₁ : D₁ ⥤ H₁}
    (σ : RA ⋙ F₁ ≅ F₀ ⋙ RB) (τ : SA ⋙ L₁ ≅ L₀ ⋙ SB)
    (α₀ : U₀ ⋙ L₀ ⟶ F₀ ⋙ V₀) (α₁ : U₁ ⋙ L₁ ⟶ F₁ ⋙ V₁)
    (ra : RA ⋙ U₁ ≅ U₀ ⋙ SA) (rb : RB ⋙ V₁ ≅ V₀ ⋙ SB)
    (γ₀ : G₀ ⋙ U₀ ≅ V₀ ⋙ R₀) (γ₁ : G₁ ⋙ U₁ ≅ V₁ ⋙ R₁)
    (ε : R₀ ⋙ SA ≅ SB ⋙ R₁)
    (h₀ : (mateEquiv a₀ b₀ α₀) = γ₀.hom)
    (h₁ : (mateEquiv a₁ b₁ α₁) = γ₁.hom)
    (hτ : (mateEquiv b₀ b₁ τ.hom) = ε.hom)
    (comm : ∀ N, U₁.map ((mateEquiv a₀ a₁ σ.hom).app N) ≫
        γ₁.hom.app (RB.obj N) ≫ R₁.map (rb.hom.app N) =
      ra.hom.app (G₀.obj N) ≫ SA.map (γ₀.hom.app N) ≫ ε.hom.app (V₀.obj N))
    (M : C₀) :
    α₁.app (RA.obj M) ≫ V₁.map (σ.hom.app M) ≫ rb.hom.app (F₀.obj M) =
      L₁.map (ra.hom.app M) ≫ τ.hom.app (U₀.obj M) ≫ SB.map (α₀.app M) := by
  have rc (N : D₀) :
      ra.inv.app (G₀.obj N) ≫ U₁.map ((mateEquiv a₀ a₁ σ.hom).app N) ≫
        (mateEquiv a₁ b₁ α₁).app (RB.obj N) =
      SA.map ((mateEquiv a₀ b₀ α₀).app N) ≫
        (mateEquiv b₀ b₁ τ.hom).app (V₀.obj N) ≫ R₁.map (rb.inv.app N) := by
    rw [show mateEquiv a₀ b₀ α₀ = .mk _ _ _ _ γ₀.hom from h₀,
      show mateEquiv a₁ b₁ α₁ = .mk _ _ _ _ γ₁.hom from h₁,
      show mateEquiv b₀ b₁ τ.hom = .mk _ _ _ _ ε.hom from hτ]
    have hh := inverse_face (ra.app (G₀.obj N)) (R₁.mapIso (rb.app N))
      (U₁.map ((mateEquiv a₀ a₁ σ.hom).app N) ≫ γ₁.hom.app (RB.obj N))
      (SA.map (γ₀.hom.app N) ≫ ε.hom.app (V₀.obj N))
      (by simpa only [Category.assoc, Iso.app_hom, Functor.mapIso_hom] using
        (comm N).symm)
    simpa only [Category.assoc, Iso.app_inv, Functor.mapIso_inv] using hh
  have he := mateEquiv_app_cube_converse a₀ a₁ b₀ b₁
    σ.hom τ.hom α₀ α₁ ra.inv rb.inv rc M
  have hh := inverse_face (L₁.mapIso (ra.app M)).symm (rb.app (F₀.obj M)).symm
    (τ.hom.app (U₀.obj M) ≫ SB.map (α₀.app M))
    (α₁.app (RA.obj M) ≫ V₁.map (σ.hom.app M))
    (by simpa only [Category.assoc, Iso.symm_hom, Iso.app_inv,
      Functor.mapIso_inv] using he)
  simpa only [Category.assoc, Iso.symm_inv, Iso.app_hom, Functor.mapIso_hom] using hh.symm

end InverseCube

section SquareFactors
variable {A B Ap Bp : Type*}
  [Category A] [Category B] [Category Ap] [Category Bp]
  [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory Ap] [HasDerivedCategory Bp]
-- Normalize the four exact-derived factorization isomorphisms.
private theorem brown_squareFactors
    (Fp : Bp ⥤ Ap) (F : B ⥤ A) (r : Ap ⥤ A) (s : Bp ⥤ B)
    [Fp.Additive] [F.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits Fp] [PreservesFiniteColimits Fp]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (hF : Fp ⋙ r ≅ s ⋙ F) (K : CochainComplex Bp ℤ) :
    (Functor.mapDerivedCategorySquareIso hF).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map (s.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj K) =
      r.mapDerivedCategory.map (Fp.mapDerivedCategoryFactors.hom.app K) ≫
        r.mapDerivedCategoryFactors.hom.app ((Fp.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex hF (.up ℤ)).hom.app K) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso Fp r).inv.app
    (DerivedCategory.Q.obj K))).mp
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [← Category.assoc]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

end SquareFactors

private local instance brown_generic_pullback_continuous
    {V W : Scheme.{u}} (g : V ⟶ W) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      W.smallEtaleTopology V.smallEtaleTopology := Etale.isContinuous_overPullback g

section GenericOrdinaryCube

private abbrev brownGenericLevel (W : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :=
  SheafOfModules.{u + 1}
    ((sheafCompose W.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of R)))

private abbrev brownGenericUnderlying (W : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    brownGenericLevel W R ⥤ Sheaf W.smallEtaleTopology (Type (u + 1)) :=
  toSheaf _ ⋙ sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})

private abbrev brownGenericRestriction (W : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) :
    brownGenericLevel W S ⥤ brownGenericLevel W R :=
  SheafOfModules.restrictScalars
    ((sheafCompose W.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)))

private abbrev brownGenericRestrictionUnderlying (W : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) :
    brownGenericRestriction W φ ⋙ brownGenericUnderlying W R ≅ brownGenericUnderlying W S :=
  isoWhiskerRight (siteScalarUnderlyingIso
    ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)))
    (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))

private theorem brown_generic_right_cube
    (R S : Type (u + 1)) [CommRing R] [CommRing S] (φ : R →+* S)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (Gm : brownGenericLevel V S ⥤ brownGenericLevel W S)
    (Gn : brownGenericLevel V R ⥤ brownGenericLevel W R)
    (α : Gm ⋙ brownGenericRestriction W φ ⟶ brownGenericRestriction V φ ⋙ Gn)
    (γm : Gm ⋙ brownGenericUnderlying W S ≅ brownGenericUnderlying V S ⋙
      (MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        (Type (u + 1)) W.smallEtaleTopology V.smallEtaleTopology)
    (γn : Gn ⋙ brownGenericUnderlying W R ≅ brownGenericUnderlying V R ⋙
      (MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        (Type (u + 1)) W.smallEtaleTopology V.smallEtaleTopology)
    (rW : brownGenericRestriction W φ ⋙ Etale.SystemProjection.constantModule W (.of R) ≅
      Etale.SystemProjection.constantModule W (.of S) ⋙
        Sheaf.restrictScalars W.smallEtaleTopology φ)
    (rV : brownGenericRestriction V φ ⋙ Etale.SystemProjection.constantModule V (.of R) ≅
      Etale.SystemProjection.constantModule V (.of S) ⋙
        Sheaf.restrictScalars V.smallEtaleTopology φ)
    (dm : Gm ⋙ Etale.SystemProjection.constantModule W (.of S) ≅
      Etale.SystemProjection.constantModule V (.of S) ⋙ Etale.lowerStar (ModuleCat S) g)
    (dn : Gn ⋙ Etale.SystemProjection.constantModule W (.of R) ≅
      Etale.SystemProjection.constantModule V (.of R) ⋙ Etale.lowerStar (ModuleCat R) g)
    (hraw : ∀ N,
      (brownGenericUnderlying W R).map (α.app N) ≫
        γn.hom.app ((brownGenericRestriction V φ).obj N) ≫
        ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
          (Type (u + 1)) W.smallEtaleTopology V.smallEtaleTopology).map
            ((brownGenericRestrictionUnderlying V φ).hom.app N) =
      (brownGenericRestrictionUnderlying W φ).hom.app (Gm.obj N) ≫ γm.hom.app N)
    (hrW : ∀ (M : brownGenericLevel W S) (U : W.Etaleᵒᵖ) (x : M.val.obj U),
      HEq ((rW.hom.app M).hom.app U x) x)
    (hrV : ∀ (M : brownGenericLevel V S) (U : V.Etaleᵒᵖ) (x : M.val.obj U),
      HEq ((rV.hom.app M).hom.app U x) x)
    (hdm : ∀ (N : brownGenericLevel V S) (U : W.Etaleᵒᵖ) (x : (Gm.obj N).val.obj U),
      (dm.hom.app N).hom.app U x = (γm.hom.app N).hom.app U x)
    (hdn : ∀ (N : brownGenericLevel V R) (U : W.Etaleᵒᵖ) (x : (Gn.obj N).val.obj U),
      (dn.hom.app N).hom.app U x = (γn.hom.app N).hom.app U x)
    (N : brownGenericLevel V S) :
    (Etale.SystemProjection.constantModule W (.of R)).map (α.app N) ≫
        dn.hom.app ((brownGenericRestriction V φ).obj N) ≫
        (Etale.lowerStar (ModuleCat R) g).map (rV.hom.app N) =
      rW.hom.app (Gm.obj N) ≫
        (Sheaf.restrictScalars W.smallEtaleTopology φ).map (dm.hom.app N) ≫
        (Etale.lowerStarRestrictScalarsIso φ g).hom.app
          ((Etale.SystemProjection.constantModule V (.of S)).obj N) := by
  ext U x
  have hu := congrArg (fun z ↦ z.hom.app U x) (hraw N)
  change (γn.hom.app _).hom.app U ((α.app N).val.app U x) =
    (γm.hom.app N).hom.app U x at hu
  have hw := hrW (Gm.obj N) U x
  have hv := hrV N ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U)
    ((dn.hom.app _).hom.app U ((α.app N).val.app U x))
  change (rV.hom.app N).hom.app
      ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U)
      ((dn.hom.app _).hom.app U ((α.app N).val.app U x)) =
    (dm.hom.app N).hom.app U ((rW.hom.app _).hom.app U x)
  calc
    _ = (dn.hom.app _).hom.app U ((α.app N).val.app U x) := eq_of_heq hv
    _ = (γn.hom.app _).hom.app U ((α.app N).val.app U x) := hdn _ U _
    _ = (γm.hom.app N).hom.app U x := hu
    _ = (dm.hom.app N).hom.app U x := (hdm N U x).symm
    _ = _ := congrArg ((dm.hom.app N).hom.app U) (eq_of_heq hw).symm

end GenericOrdinaryCube

-- Form the section predicate before specializing to the quotient coefficient rings.
private def brown_generic_restriction_section_law
    (W : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
    (r : brownGenericRestriction W φ ⋙ Etale.SystemProjection.constantModule W (.of R) ≅
      Etale.SystemProjection.constantModule W (.of S) ⋙
        Sheaf.restrictScalars W.smallEtaleTopology φ) : Prop :=
  ∀ (M : brownGenericLevel W S) (U : W.Etaleᵒᵖ) (x : M.val.obj U),
    HEq ((r.hom.app M).hom.app U x) x

-- The section law is independent of the derived coherence fields.
private def brown_restriction_section_law
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) (R : StrictEtaleBrownRealizationData O t W P) : Prop :=
  ∀ {m n : ℕ} (h : m ≤ n),
    brown_generic_restriction_section_law W (strictEtaleBrownRingMap O t h)
      (R.ordinaryRestriction h)

-- Keep the localization and mate laws shared when projecting the ordinary section law.
private def brown_restriction_derived_laws
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) (R : StrictEtaleBrownRealizationData O t W P) : Prop :=
  letI := R.ordinaryAdditive
  (∀ {m n : ℕ} (h : m ≤ n)
    (K : CochainComplex (strictEtaleLevel W O t m) ℤ),
    (R.restriction h).hom.app (DerivedCategory.Q.obj K) ≫
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)).map ((R.factors m).hom.app K) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors.hom.app
          (((strictEtaleBrownConstant O t W m).mapHomologicalComplex (.up ℤ)).obj K) =
    (R.derived n).map ((P.scalar h).restrictionFactors.hom.app K) ≫
      (R.factors n).hom.app
        (((coefficientRestriction (J := W.smallEtaleTopology) O t h).mapHomologicalComplex
          (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (R.ordinaryRestriction h) (.up ℤ)).hom.app K)) ∧
  (∀ {m n : ℕ} (h : m ≤ n),
    (mateEquiv (P.scalar h).derivedAdj
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)))
      (.mk _ _ _ _ (R.scalar h).inv)) = (R.restriction h).hom)

private theorem brown_restriction_coherence_iff
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) (R : StrictEtaleBrownRealizationData O t W P) :
    StrictEtaleBrownRealizationCoherence O t W P R ↔
      brown_restriction_section_law O t W P R ∧
        brown_restriction_derived_laws O t W P R := Iff.rfl

-- Project the section law without retaining the derived coherence conjunction.
private theorem brown_restriction_section_normalized
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) (R : StrictEtaleBrownRealization O t W P)
    : ∀ {m n : ℕ} (h : m ≤ n) (M : strictEtaleLevel W O t m) (U : W.Etaleᵒᵖ) (x : M.val.obj U),
      HEq (((R.val.ordinaryRestriction h).hom.app M).hom.app U x) x := by
  exact @And.left (brown_restriction_section_law O t W P R.val)
    (brown_restriction_derived_laws O t W P R.val)
    ((brown_restriction_coherence_iff O t W P R.val).mp R.property)

private theorem brown_right_section_normalized
    (O : Type (u + 1)) [CommRing O] (t : O) {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV) (RW : StrictEtaleBrownRealization O t W PW)
    (r : StrictEtaleBrownImageRealization O t g n A B RV RW) :
    ∀ (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
      (x : ((A.right n).obj M).val.obj U),
      ((r.val.ordinaryRight.hom.app M).hom.app U x) =
        ((A.rightUnderlying n).hom.app M).hom.app U x :=
  r.property.1

-- Cache the derived restriction normalization before specializing a cube face.
private theorem brown_restriction_derived_normalized
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) (R : StrictEtaleBrownRealization O t W P) :
    letI := R.val.ordinaryAdditive
    ∀ {m n : ℕ} (h : m ≤ n) (K : CochainComplex (strictEtaleLevel W O t m) ℤ),
    (R.val.restriction h).hom.app (DerivedCategory.Q.obj K) ≫
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)).map ((R.factors m).hom.app K) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors.hom.app
          (((strictEtaleBrownConstant O t W m).mapHomologicalComplex (.up ℤ)).obj K) =
    (R.derived n).map ((P.scalar h).restrictionFactors.hom.app K) ≫
      (R.factors n).hom.app
        (((coefficientRestriction (J := W.smallEtaleTopology) O t h).mapHomologicalComplex
          (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (R.val.ordinaryRestriction h) (.up ℤ)).hom.app K) :=
  R.property.2.1

section OrdinaryCube
variable (O : Type (u + 1)) [CommRing O] (t : O)
  {V W : Scheme.{u}} (g : V ⟶ W) (A : StrictEtaleOrdinaryImage O t g)
  (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
  (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
    (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
  (RV : StrictEtaleBrownRealization O t V PV)
  (RW : StrictEtaleBrownRealization O t W PW)
  (rg : ∀ k, StrictEtaleBrownImageRealization O t g k A (B.level k) RV RW)
  {m n : ℕ} (h : m ≤ n)

-- Comparing the two transported ordinary adjunctions unfolds coefficient equivalences.
private theorem ordinary_inverse_isIso (k : ℕ) :
    IsIso (strictEtaleBrownOrdinaryInverse O t g k A (B.level k) (rg k)) := by
  let := constant_equivalence O t W k
  let := constant_equivalence O t V k
  exact isIso_inverseMate_of_equivalences (A.levelAdj k)
    (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) g) (rg k).val.ordinaryRight

private noncomputable def ordinary_inverse_iso (k : ℕ) :
    strictEtaleBrownConstant O t W k ⋙
        Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) g ≅
      (A.lift k).modules ⋙ strictEtaleBrownConstant O t V k := by
  let : IsIso (strictEtaleBrownOrdinaryInverse O t g k A (B.level k) (rg k)) :=
    ordinary_inverse_isIso O t g A PW PV B RV RW rg k
  exact asIso (strictEtaleBrownOrdinaryInverse O t g k A (B.level k) (rg k))

private theorem ordinary_inverse_iso_hom (k : ℕ) :
    (ordinary_inverse_iso O t g A PW PV B RV RW rg k).hom =
      strictEtaleBrownOrdinaryInverse O t g k A (B.level k) (rg k) := by
  rfl

-- Keep the abstract sheaf equation opaque before evaluation on sections.
private theorem ordinary_underlying_raw (N : strictEtaleLevel V O t m) :
    (coefficientUnderlying (J := W.smallEtaleTopology) O t n).map
        ((mateEquiv (A.levelAdj m) (A.levelAdj n)
          (.mk _ _ _ _ (A.restrictInverse h).hom)).app N) ≫
      (A.rightUnderlying n).hom.app
        ((coefficientRestriction (J := V.smallEtaleTopology) O t h).obj N) ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        (Type (u + 1)) W.smallEtaleTopology V.smallEtaleTopology).map
          ((coefficientRestrictionUnderlying (J := V.smallEtaleTopology) O t h).hom.app N) =
    (coefficientRestrictionUnderlying (J := W.smallEtaleTopology) O t h).hom.app
        ((A.right m).obj N) ≫ (A.rightUnderlying m).hom.app N := by
  exact brownRestrictionMate_underlying
    (A.lift m).modules (A.right m) (A.levelAdj m)
    (A.lift n).modules (A.right n) (A.levelAdj n)
    (coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (coefficientUnderlying (J := W.smallEtaleTopology) O t n)
    (coefficientUnderlying (J := W.smallEtaleTopology) O t m)
    (coefficientUnderlying (J := V.smallEtaleTopology) O t n)
    (coefficientUnderlying (J := V.smallEtaleTopology) O t m)
    _ _ (strictEtaleSetAdjunction g)
    (coefficientRestrictionUnderlying (J := W.smallEtaleTopology) O t h)
    (coefficientRestrictionUnderlying (J := V.smallEtaleTopology) O t h)
    (A.lift m).moduleUnderlying (A.lift n).moduleUnderlying
    (A.rightUnderlying m) (A.rightUnderlying n) (A.restrictInverse h)
    (A.levelTranspose m) (A.levelTranspose n) (A.restrictInverseUnderlying h) N

-- Compare the ordinary right-adjoint restriction cube on underlying sections.
private theorem ordinary_right_cube (N : strictEtaleLevel V O t m) :
    (strictEtaleBrownConstant O t W n).map
        ((mateEquiv (A.levelAdj m) (A.levelAdj n)
          (.mk _ _ _ _ (A.restrictInverse h).hom)).app N) ≫
      (rg n).val.ordinaryRight.hom.app
        ((coefficientRestriction (J := V.smallEtaleTopology) O t h).obj N) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).map
        ((RV.val.ordinaryRestriction h).hom.app N) =
    (RW.val.ordinaryRestriction h).hom.app ((A.right m).obj N) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h)).map
        ((rg m).val.ordinaryRight.hom.app N) ≫
      (Etale.lowerStarRestrictScalarsIso (strictEtaleBrownRingMap O t h) g).hom.app
        ((strictEtaleBrownConstant O t V m).obj N) := by
  exact brown_generic_right_cube (strictEtaleBrownRing O t n)
    (strictEtaleBrownRing O t m) (strictEtaleBrownRingMap O t h) g
    (A.right m) (A.right n)
    (mateEquiv (A.levelAdj m) (A.levelAdj n)
      (.mk _ _ _ _ (A.restrictInverse h).hom))
    (A.rightUnderlying m) (A.rightUnderlying n)
    (RW.val.ordinaryRestriction h) (RV.val.ordinaryRestriction h)
    (rg m).val.ordinaryRight (rg n).val.ordinaryRight
    (fun N ↦ ordinary_underlying_raw O t g A h N)
    (fun M U x ↦ brown_restriction_section_normalized O t W PW RW h M U x)
    (fun M U x ↦ brown_restriction_section_normalized O t V PV RV h M U x)
    (fun M U x ↦ brown_right_section_normalized O t g m A (B.level m) RV RW
      (rg m) M U x)
    (fun M U x ↦ brown_right_section_normalized O t g n A (B.level n) RV RW
      (rg n) M U x) N

-- Compare ordinary sectionwise normalizations with the abstract inverse-mate cube.
private theorem ordinary_inverse_cube (M : strictEtaleLevel W O t m) :
    (strictEtaleBrownOrdinaryInverse O t g n A (B.level n) (rg n)).app
        ((coefficientRestriction (J := W.smallEtaleTopology) O t h).obj M) ≫
      (strictEtaleBrownConstant O t V n).map ((A.restrictInverse h).hom.app M) ≫
      (RV.val.ordinaryRestriction h).hom.app ((A.lift m).modules.obj M) =
    (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).map
        ((RW.val.ordinaryRestriction h).hom.app M) ≫
      (Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g).hom.app
        ((strictEtaleBrownConstant O t W m).obj M) ≫
      (Sheaf.restrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h)).map
        ((strictEtaleBrownOrdinaryInverse O t g m A (B.level m) (rg m)).app M) := by
  apply brown_inverse_cube (A.levelAdj m) (A.levelAdj n)
    (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g)
    (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (A.restrictInverse h)
    (Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g)
    (strictEtaleBrownOrdinaryInverse O t g m A (B.level m) (rg m))
    (strictEtaleBrownOrdinaryInverse O t g n A (B.level n) (rg n))
    (RW.val.ordinaryRestriction h) (RV.val.ordinaryRestriction h)
    (rg m).val.ordinaryRight (rg n).val.ordinaryRight
    (Etale.lowerStarRestrictScalarsIso (strictEtaleBrownRingMap O t h) g)
    (((mateEquiv _ _).apply_symm_apply _))
    (((mateEquiv _ _).apply_symm_apply _))
    (Etale.underived_mate (strictEtaleBrownRingMap O t h) g)
    (ordinary_right_cube O t g A PW PV B RV RW rg h) M

-- Specialize the inverse-face identity to the ordinary comparisons.
private theorem ordinary_inverse_symm_cube (M : strictEtaleLevel W O t m) :
      (strictEtaleBrownConstant O t V n).map ((A.restrictInverse h).hom.app M) ≫
        (RV.val.ordinaryRestriction h).hom.app ((A.lift m).modules.obj M) ≫
        (Sheaf.restrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h)).map
          ((ordinary_inverse_iso O t g A PW PV B RV RW rg m).inv.app M) =
      (ordinary_inverse_iso O t g A PW PV B RV RW rg n).inv.app
          ((coefficientRestriction (J := W.smallEtaleTopology) O t h).obj M) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).map
          ((RW.val.ordinaryRestriction h).hom.app M) ≫
        (Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g).hom.app
          ((strictEtaleBrownConstant O t W m).obj M) := by
  let φ := strictEtaleBrownRingMap O t h
  let FW k := Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) g
  let CW k := strictEtaleBrownConstant O t W k
  let CV k := strictEtaleBrownConstant O t V k
  let ii k := ordinary_inverse_iso O t g A PW PV B RV RW rg k
  have hh := ordinary_inverse_cube O t g A PW PV B RV RW rg h M
  let r := Sheaf.restrictScalars V.smallEtaleTopology φ
  change (ii n).hom.app
    ((coefficientRestriction (J := W.smallEtaleTopology) O t h).obj M) ≫
      (CV n).map ((A.restrictInverse h).hom.app M) ≫
      (RV.val.ordinaryRestriction h).hom.app ((A.lift m).modules.obj M) =
    (FW n).map ((RW.val.ordinaryRestriction h).hom.app M) ≫
      (Etale.upperStarRestrictScalarsIsoSheaf φ g).hom.app ((CW m).obj M) ≫
      r.map ((ii m).hom.app M) at hh
  have hs := inverse_face
    ((ii n).app ((coefficientRestriction (J := W.smallEtaleTopology) O t h).obj M))
    (r.mapIso ((ii m).app M))
    ((FW n).map ((RW.val.ordinaryRestriction h).hom.app M) ≫
      (Etale.upperStarRestrictScalarsIsoSheaf φ g).hom.app ((CW m).obj M))
    ((CV n).map ((A.restrictInverse h).hom.app M) ≫
      (RV.val.ordinaryRestriction h).hom.app ((A.lift m).modules.obj M))
    (by simpa only [Category.assoc, Iso.app_hom, Functor.mapIso_hom] using hh)
  simpa only [Category.assoc, Iso.app_inv, Functor.mapIso_inv] using hs.symm

end OrdinaryCube

-- Invert the normalized cochain comparison at the exact functor factors.
private theorem brown_inverse_cochain_face
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ k, StrictEtaleBrownImageRealization O t g k A (B.level k) RV RW)
    (hinverse : ∀ k (K : CochainComplex (strictEtaleLevel W O t k) ℤ),
      letI : (strictEtaleBrownConstant O t V k).Additive := RV.val.ordinaryAdditive k
      letI : (strictEtaleBrownConstant O t W k).Additive := RW.val.ordinaryAdditive k
      letI : Functor.PreservesZeroMorphisms
          ((A.lift k).modules ⋙ strictEtaleBrownConstant O t V k) :=
        Functor.preservesZeroMorphisms_comp _ _
      (rg k).inverse.hom.app (DerivedCategory.Q.obj K) ≫
          (RV.derived k).map ((B.level k).inverseFactors.hom.app K) ≫
          (RV.factors k).hom.app
            (((A.lift k).modules.mapHomologicalComplex (.up ℤ)).obj K) =
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
          g).mapDerivedCategory.map ((RW.factors k).hom.app K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
            g).mapDerivedCategoryFactors.hom.app
            (((strictEtaleBrownConstant O t W k).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (strictEtaleBrownOrdinaryInverse O t g k A (B.level k) (rg k))
              (.up ℤ)).app K)) :
    letI := RV.val.ordinaryAdditive
    letI := RW.val.ordinaryAdditive
    letI : ∀ k, Functor.PreservesZeroMorphisms
        ((A.lift k).modules ⋙ strictEtaleBrownConstant O t V k) :=
      fun _k ↦ Functor.preservesZeroMorphisms_comp _ _
    ∀ k (K : CochainComplex (strictEtaleLevel W O t k) ℤ),
      (rg k).inverse.inv.app (DerivedCategory.Q.obj K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
          g).mapDerivedCategory.map ((RW.factors k).hom.app K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
          g).mapDerivedCategoryFactors.hom.app
          (((strictEtaleBrownConstant O t W k).mapHomologicalComplex (.up ℤ)).obj K) =
      (RV.derived k).map ((B.level k).inverseFactors.hom.app K) ≫
        (RV.factors k).hom.app
          (((A.lift k).modules.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (ordinary_inverse_iso O t g A PW PV B RV RW rg k).symm (.up ℤ)).hom.app K) := by
  dsimp only
  let := RV.val.ordinaryAdditive
  let := RW.val.ordinaryAdditive
  let FW k := Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) g
  let CW k := strictEtaleBrownConstant O t W k
  let CV k := strictEtaleBrownConstant O t V k
  let (k : ℕ) : Functor.PreservesZeroMorphisms
      ((A.lift k).modules ⋙ CV k) := Functor.preservesZeroMorphisms_comp _ _
  let ii k := ordinary_inverse_iso O t g A PW PV B RV RW rg k
  intro k K
  have hh := inverse_face ((rg k).inverse.app (DerivedCategory.Q.obj K))
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (ii k) (.up ℤ)).app K))
    ((FW k).mapDerivedCategory.map ((RW.factors k).hom.app K) ≫
      (FW k).mapDerivedCategoryFactors.hom.app
        (((CW k).mapHomologicalComplex (.up ℤ)).obj K))
    ((RV.derived k).map ((B.level k).inverseFactors.hom.app K) ≫
      (RV.factors k).hom.app
        (((A.lift k).modules.mapHomologicalComplex (.up ℤ)).obj K))
    (by simpa only [Category.assoc, Iso.app_hom, Functor.mapIso_hom,
      NatIso.mapHomologicalComplex, ii, ordinary_inverse_iso_hom] using hinverse k K)
  simpa only [Category.assoc, Iso.app_inv, Functor.mapIso_inv,
    NatIso.mapHomologicalComplex, Iso.symm_hom] using hh

-- Specialize the ordinary-functor localization cube to coefficient sheaves.
private theorem brown_exact_restriction_cube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ k, StrictEtaleBrownImageRealization O t g k A (B.level k) RV RW)
    (hinverse : ∀ k (K : CochainComplex (strictEtaleLevel W O t k) ℤ),
      letI : (strictEtaleBrownConstant O t V k).Additive := RV.val.ordinaryAdditive k
      letI : (strictEtaleBrownConstant O t W k).Additive := RW.val.ordinaryAdditive k
      letI : Functor.PreservesZeroMorphisms
          ((A.lift k).modules ⋙ strictEtaleBrownConstant O t V k) :=
        Functor.preservesZeroMorphisms_comp _ _
      (rg k).inverse.hom.app (DerivedCategory.Q.obj K) ≫
          (RV.derived k).map ((B.level k).inverseFactors.hom.app K) ≫
          (RV.factors k).hom.app
            (((A.lift k).modules.mapHomologicalComplex (.up ℤ)).obj K) =
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
          g).mapDerivedCategory.map ((RW.factors k).hom.app K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
            g).mapDerivedCategoryFactors.hom.app
            (((strictEtaleBrownConstant O t W k).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (strictEtaleBrownOrdinaryInverse O t g k A (B.level k) (rg k))
              (.up ℤ)).app K))
    {m n : ℕ} (h : m ≤ n) :
    ∀ X : DerivedCategory (strictEtaleLevel W O t m),
      (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        g).mapDerivedCategory.map ((RW.val.restriction h).hom.app X) ≫
        (Functor.mapDerivedCategorySquareIso
          (Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g)).hom.app
            ((RW.derived m).obj X) ≫
        (Sheaf.derivedRestrictScalars V.smallEtaleTopology
          (strictEtaleBrownRingMap O t h)).map ((rg m).inverse.hom.app X) =
      (rg n).inverse.hom.app ((PW.scalar h).restriction.obj X) ≫
        (RV.derived n).map
          ((strictEtaleBrownCanonicalRestriction O t g A PW PV B h).hom.app X) ≫
        (RV.val.restriction h).hom.app ((B.level m).inverse.obj X) := by
  let := RV.val.ordinaryAdditive
  let := RW.val.ordinaryAdditive
  let φ := strictEtaleBrownRingMap O t h
  let FW k := Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) g
  let CW k := strictEtaleBrownConstant O t W k
  let CV k := strictEtaleBrownConstant O t V k
  let (k : ℕ) : Functor.PreservesZeroMorphisms
      ((A.lift k).modules ⋙ CV k) := Functor.preservesZeroMorphisms_comp _ _
  let ii k := ordinary_inverse_iso O t g A PW PV B RV RW rg k
  have fac := brown_inverse_cochain_face O t g A PW PV B RV RW rg hinverse
  have hcan (K : CochainComplex
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))) ℤ) :=
    brown_squareFactors (Sheaf.restrictScalars W.smallEtaleTopology φ)
      (Sheaf.restrictScalars V.smallEtaleTopology φ) (FW n) (FW m)
      (Etale.upperStarRestrictScalarsIsoSheaf φ g) K
  have ordinary (M : strictEtaleLevel W O t m) :
      (strictEtaleBrownConstant O t V n).map ((A.restrictInverse h).hom.app M) ≫
        (RV.val.ordinaryRestriction h).hom.app ((A.lift m).modules.obj M) ≫
        (Sheaf.restrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h)).map
          ((ii m).inv.app M) =
      (ii n).inv.app ((coefficientRestriction (J := W.smallEtaleTopology) O t h).obj M) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).map
          ((RW.val.ordinaryRestriction h).hom.app M) ≫
        (Etale.upperStarRestrictScalarsIsoSheaf (strictEtaleBrownRingMap O t h) g).hom.app
          ((strictEtaleBrownConstant O t W m).obj M) := by
    exact ordinary_inverse_symm_cube O t g A PW PV B RV RW rg h M
  exact brown_cochain_normalized_cube
    (QC := DerivedCategory.Q) (QD := DerivedCategory.Q)
    (QE := DerivedCategory.Q) (QF := DerivedCategory.Q)
    (QG := DerivedCategory.Q) (QH := DerivedCategory.Q)
    (QI := DerivedCategory.Q) (QJ := DerivedCategory.Q)
    (a := coefficientRestriction (J := W.smallEtaleTopology) O t h)
    (aD := (PW.scalar h).restriction)
    (b := (A.lift n).modules)
    (bD := (B.level n).inverse)
    (c := CV n) (cD := RV.derived n)
    (d := (A.lift m).modules)
    (dD := (B.level m).inverse)
    (e := coefficientRestriction (J := V.smallEtaleTopology) O t h)
    (eD := (PV.scalar h).restriction)
    (f := CV m) (fD := RV.derived m)
    (g := Sheaf.restrictScalars V.smallEtaleTopology φ)
    (gD := Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
    (h := CW m) (hD := RW.derived m)
    (i := FW m) (iD := (FW m).mapDerivedCategory)
    (j := CW n) (jD := RW.derived n)
    (k := FW n) (kD := (FW n).mapDerivedCategory)
    (m := Sheaf.restrictScalars W.smallEtaleTopology φ)
    (mD := Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
    (φa := (PW.scalar h).restrictionFactors)
    (φb := (B.level n).inverseFactors) (φc := RV.factors n)
    (φd := (B.level m).inverseFactors) (φe := (PV.scalar h).restrictionFactors)
    (φf := RV.factors m)
    (φg := (Sheaf.restrictScalars V.smallEtaleTopology φ).mapDerivedCategoryFactors)
    (φh := RW.factors m) (φi := (FW m).mapDerivedCategoryFactors)
    (φj := RW.factors n)
    (φk := (FW n).mapDerivedCategoryFactors)
    (φm := (Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryFactors)
    (q1 := (A.restrictInverse h))
    (s1 := strictEtaleBrownCanonicalRestriction O t g A PW PV B h)
    (h1 := strictEtaleBrownCanonicalRestriction_rep O t g A PW PV B h)
    (q2 := (RV.val.ordinaryRestriction h))
    (s2 := RV.val.restriction h) (h2 := brown_restriction_derived_normalized O t V PV RV h)
    (q3 := (ii m).symm)
    (s3 := (rg m).inverse.symm) (h3 := fac m)
    (q4 := (ii n).symm)
    (s4 := (rg n).inverse.symm) (h4 := fac n)
    (q5 := (RW.val.ordinaryRestriction h))
    (s5 := RW.val.restriction h) (h5 := brown_restriction_derived_normalized O t W PW RW h)
    (q6 := (Etale.upperStarRestrictScalarsIsoSheaf φ g))
    (s6 := Functor.mapDerivedCategorySquareIso
      (Etale.upperStarRestrictScalarsIsoSheaf φ g)) (h6 := hcan)
    (comm := ordinary)

-- The localization cube simultaneously compares twelve factorization isomorphisms.
/-- The exact ordinary restriction cube commutes after Brown realization.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CY, 05RU and 07A4.
(blueprint: lem-pur-etale-brown-canonical-restriction-cube).

Proof: compare the ordinary inverse mates of the specified direct-image
comparisons at the two coefficient levels. The section equation for those
comparisons identifies their underlying maps with A.rightUnderlying. Transpose
using A.levelTranspose and the geometric sheaf adjunctions. The equation
A.restrictInverseUnderlying identifies the two composites after forgetting scalar
structure; the ordinaryRestriction comparisons are identities on these sections.
Faithfulness gives the ordinary restriction cube. Apply cochain prolongation and
localization. Postcompose both derived composites with the invertible realization
factor of the common target. Naturality and the canonical restriction representative
equation identify its first face; hinverse identifies the geometric faces; the
Brown restriction representative equations identify its remaining faces. The
ordinary cube makes the resulting cochain maps equal. Fully faithful
precomposition with Q extends the equality to all derived objects. Finally
transport the two geometric faces along the exact-to-left-derived pullback
isomorphisms. The definition of scalarRestrictionPullbackIso cancels these
comparison factors and gives the displayed equation. This uses neither properness
nor finiteness, nor the scalar inverse mate or its invertibility. -/
theorem strictEtaleBrownCanonicalRestrictionCube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ k, StrictEtaleBrownImageRealization O t g k A (B.level k) RV RW)
    (hinverse : ∀ k (K : CochainComplex (strictEtaleLevel W O t k) ℤ),
      letI : (strictEtaleBrownConstant O t V k).Additive := RV.val.ordinaryAdditive k
      letI : (strictEtaleBrownConstant O t W k).Additive := RW.val.ordinaryAdditive k
      letI : Functor.PreservesZeroMorphisms
          ((A.lift k).modules ⋙ strictEtaleBrownConstant O t V k) :=
        Functor.preservesZeroMorphisms_comp _ _
      (rg k).inverse.hom.app (DerivedCategory.Q.obj K) ≫
          (RV.derived k).map ((B.level k).inverseFactors.hom.app K) ≫
          (RV.factors k).hom.app
            (((A.lift k).modules.mapHomologicalComplex (.up ℤ)).obj K) =
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
          g).mapDerivedCategory.map ((RW.factors k).hom.app K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
            g).mapDerivedCategoryFactors.hom.app
            (((strictEtaleBrownConstant O t W k).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (strictEtaleBrownOrdinaryInverse O t g k A (B.level k) (rg k))
              (.up ℤ)).app K))
    {m n : ℕ} (h : m ≤ n) :
    let pn := (rg n).inverse.symm ≪≫ isoWhiskerLeft (RW.derived n)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).symm
    let pm := (rg m).inverse.symm ≪≫ isoWhiskerLeft (RW.derived m)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g).symm
    ∀ X : DerivedCategory (strictEtaleLevel W O t m),
      pn.inv.app ((PW.scalar h).restriction.obj X) ≫
          (RV.derived n).map
            ((strictEtaleBrownCanonicalRestriction O t g A PW PV B h).hom.app X) ≫
          (RV.val.restriction h).hom.app ((B.level m).inverse.obj X) =
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
          g).leftDerivedFunctor.map ((RW.val.restriction h).hom.app X) ≫
          (Etale.scalarRestrictionPullbackIso (strictEtaleBrownRingMap O t h) g).hom.app
            ((RW.derived m).obj X) ≫
          (Sheaf.derivedRestrictScalars V.smallEtaleTopology
            (strictEtaleBrownRingMap O t h)).map (pm.inv.app X) := by
  dsimp only
  intro X
  let φ := strictEtaleBrownRingMap O t h
  have hmap := brown_exact_restriction_cube O t g A PW PV B RV RW rg hinverse h X
  have ht := brown_transport_cube
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g)
    (Functor.mapDerivedCategorySquareIso
      (Etale.upperStarRestrictScalarsIsoSheaf φ g))
    ((rg n).inverse.app ((PW.scalar h).restriction.obj X))
    ((rg m).inverse.app X) ((RW.val.restriction h).hom.app X)
    ((RV.derived n).map
        ((strictEtaleBrownCanonicalRestriction O t g A PW PV B h).hom.app X) ≫
      (RV.val.restriction h).hom.app ((B.level m).inverse.obj X)) hmap
  simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, isoWhiskerLeft_inv,
    whiskerLeft_app, Category.assoc, Iso.app_hom, Etale.scalarRestrictionPullbackIso] using ht

end AlgebraicGeometry
