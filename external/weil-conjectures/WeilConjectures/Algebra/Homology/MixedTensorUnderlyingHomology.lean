/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Underlying additive homology of mixed total tensors

Source: Stacks Project, Tag 06Y6, the ordinary balanced tensor identifications.
(blueprint: new-lem-pc-mixed-tensor-underlying-homology).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology

open MonoidalCategory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def coeff (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj
      (((ModuleCat.mixedTensor (algebraMap R A)).obj M).obj N) ≅
      (ModuleCat.restrictScalars (algebraMap R A)).obj M ⊗ N := by
  let : Algebra R A := (algebraMap R A).toAlgebra
  let : Module R M := Module.compHom M (algebraMap R A)
  let : IsScalarTower R A M := SMul.comp.isScalarTower (algebraMap R A)
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M N).restrictScalars R
    |>.toModuleIso

private theorem coeff_left (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {M M' : ModuleCat.{u} A} (g : M ⟶ M') (N : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R A)).map
        (((ModuleCat.mixedTensor (algebraMap R A)).map g).app N) ≫
      (coeff R A M' N).hom =
    (coeff R A M N).hom ≫
      ((ModuleCat.restrictScalars (algebraMap R A)).map g ▷ N) := by
  let : Algebra R A := (algebraMap R A).toAlgebra
  let : Module R M := Module.compHom M (algebraMap R A)
  let : Module R M' := Module.compHom M' (algebraMap R A)
  let : IsScalarTower R A M := SMul.comp.isScalarTower (algebraMap R A)
  let : IsScalarTower R A M' := SMul.comp.isScalarTower (algebraMap R A)
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp_all
  | tmul m t =>
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp_all [TensorProduct.tmul_add]
    | tmul a n =>
      change A at a
      change (a • g m) ⊗ₜ[R] n = g (a • m) ⊗ₜ[R] n
      rw [g.hom.map_smul]

private theorem coeff_right (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (M : ModuleCat.{u} A) {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    (ModuleCat.restrictScalars (algebraMap R A)).map
        (((ModuleCat.mixedTensor (algebraMap R A)).obj M).map g) ≫
      (coeff R A M N').hom =
    (coeff R A M N).hom ≫
      ((ModuleCat.restrictScalars (algebraMap R A)).obj M ◁ g) := by
  let : Algebra R A := (algebraMap R A).toAlgebra
  let : Module R M := Module.compHom M (algebraMap R A)
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp_all
  | tmul m t =>
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp_all [TensorProduct.tmul_add]
    | tmul a n => rfl

private noncomputable def bicomp (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex₂
      (.up ℤ) (.up ℤ)).obj
        ((((ModuleCat.mixedTensor (algebraMap R A)).mapBifunctorHomologicalComplex
          (.up ℤ) (.up ℤ)).obj Q).obj F) ≅
    (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj ((restrict R A).obj Q)).obj F := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p ↦
    HomologicalComplex.Hom.isoOfComponents (fun q ↦ coeff R A (Q.X p) (F.X q)) ?_) ?_
  · intro q q' h
    exact (coeff_right R A (Q.X p) (F.d q q')).symm
  · intro p p' h
    ext1 q
    exact (coeff_left R A (Q.d p p') (F.X q)).symm

private noncomputable def totalComp (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    (restrict R A).obj (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ≅
      (((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj
        ((restrict R A).obj Q)).obj F) :=
  (HomologicalComplex₂.mapTotalIso (ModuleCat.restrictScalars (algebraMap R A)) _
    (.up ℤ)).symm ≪≫ HomologicalComplex₂.total.mapIso (bicomp R A Q F) (.up ℤ)

private theorem totalComp_ι (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    (ModuleCat.restrictScalars (algebraMap R A)).map
        (HomologicalComplex.ιMapBifunctor Q F
          (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h) ≫
      (totalComp R A Q F).hom.f n =
    (coeff R A (Q.X p) (F.X q)).hom ≫
      HomologicalComplex.ιMapBifunctor ((restrict R A).obj Q) F
        (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q n h := by
  let U := ModuleCat.restrictScalars (algebraMap R A)
  let S := (((ModuleCat.mixedTensor (algebraMap R A)).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj Q).obj F
  change U.map (S.ιTotal (.up ℤ) p q n h) ≫
    (HomologicalComplex₂.mapTotalXIso U S (.up ℤ) n).inv ≫
      (HomologicalComplex₂.total.map (bicomp R A Q F).hom (.up ℤ)).f n = _
  rw [HomologicalComplex₂.map_ι_mapTotalXIso_inv_assoc, HomologicalComplex₂.ιTotal_map]
  rfl

private theorem totalComp_formula (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (p q n : ℤ) (h : p + q = n) (x : Q.X p) (y : F.X q) :
    (totalComp R A Q F).hom.f n
      ((HomologicalComplex.ιMapBifunctor Q F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h)
          (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y))) =
      (HomologicalComplex.ιMapBifunctor ((restrict R A).obj Q) F
        (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q n h) (x ⊗ₜ[R] y) := by
  have h := ConcreteCategory.congr_hom (totalComp_ι R A Q F p q n h)
    (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y))
  simp only [ModuleCat.comp_apply] at h
  let : Module R (Q.X p) := Module.compHom (Q.X p) (algebraMap R A)
  have hc : (coeff R A (Q.X p) (F.X q)).hom
      (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y)) = x ⊗ₜ[R] y := by
    let : Algebra R A := (algebraMap R A).toAlgebra
    let : Module R (Q.X p) := Module.compHom (Q.X p) (algebraMap R A)
    change (1 : A) • x ⊗ₜ[R] y = x ⊗ₜ[R] y
    rw [one_smul]
  rw [hc] at h
  exact h


private theorem mixed_underlying_ext (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (G : AddCommGrpCat.{u})
    (a b : (forget₂ (ModuleCat.{u} A) AddCommGrpCat).obj
      ((((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F).X n) ⟶ G)
    (h : ∀ (p q : ℤ) (hpq : p + q = n) (x : Q.X p) (y : F.X q),
      a ((HomologicalComplex.ιMapBifunctor Q F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n hpq)
          (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y))) =
      b ((HomologicalComplex.ιMapBifunctor Q F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n hpq)
          (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y)))) : a = b := by
  let : Algebra R A := (algebraMap R A).toAlgebra
  let U := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let S := (((ModuleCat.mixedTensor (algebraMap R A)).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj Q).obj F
  apply (cancel_epi (HomologicalComplex₂.mapTotalXIso U S (.up ℤ) n).hom).1
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rw [HomologicalComplex₂.ι_mapTotalXIso_hom_assoc,
    HomologicalComplex₂.ι_mapTotalXIso_hom_assoc]
  apply AddCommGrpCat.hom_ext
  ext t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp_all
  | tmul x t =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp_all [TensorProduct.tmul_add]
    | tmul c y =>
      change A at c
      have he : x ⊗ₜ[A] (c ⊗ₜ[R,algebraMap R A] y) =
          (c • x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y) := by
        rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul']
        simp only [smul_eq_mul, mul_one]
      change a ((S.ιTotal (.up ℤ) p q n hpq) (x ⊗ₜ[A] (c ⊗ₜ[R] y))) =
        b ((S.ιTotal (.up ℤ) p q n hpq) (x ⊗ₜ[A] (c ⊗ₜ[R] y)))
      rw [he]
      exact h p q hpq (c • x) y

private noncomputable def addComp (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ≅
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
      (((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj
        ((restrict R A).obj Q)).obj F) :=
  ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).mapIso
    (totalComp R A Q F)

private theorem addComp_naturality (R A Aq : Type u)
    [CommRing R] [CommRing A] [CommRing Aq]
    [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (Qq : CochainComplex (ModuleCat.{u} Aq) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (g : (restrict R A).obj Q ⟶ (restrict R Aq).obj Qq)
    (v : (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ⟶
      (restrict A Aq).obj (((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F))
    (hv : ∀ (p q n : ℤ) (h : p + q = n) (x : Q.X p) (y : F.X q),
      v.f n ((HomologicalComplex.ιMapBifunctor Q F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h)
          (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y))) =
      (HomologicalComplex.ιMapBifunctor Qq F
        (ModuleCat.mixedTensor (algebraMap R Aq)) (.up ℤ) p q n h)
          ((g.f p x) ⊗ₜ[Aq] ((1 : Aq) ⊗ₜ[R,algebraMap R Aq] y))) :
    ((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map v ≫
        (addComp R Aq Qq F).hom =
      (addComp R A Q F).hom ≫
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.map g).app F) := by
  ext1 n
  apply mixed_underlying_ext R A Q F n
  intro p q hpq x y
  change (totalComp R Aq Qq F).hom.f n (v.f n _) =
    (((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.map g).app F).f n
      ((totalComp R A Q F).hom.f n _)
  rw [hv, totalComp_formula, totalComp_formula]
  let : Module R (Q.X p) := Module.compHom (Q.X p) (algebraMap R A)
  have ht := ConcreteCategory.congr_hom
    (HomologicalComplex.ι_mapBifunctorMap
      g (𝟙 F) (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q n hpq) (x ⊗ₜ[R] y)
  simp only [ModuleCat.comp_apply] at ht
  exact ht.symm

private theorem iteratedHomologyData_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (S : ShortComplex C) [S.HasHomology] (h : S.LeftHomologyData)
    (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    ((h.map F).map G).cyclesIso.hom = (h.map (F ⋙ G)).cyclesIso.hom ∧
      ((h.map F).map G).homologyIso.hom = (h.map (F ⋙ G)).homologyIso.hom := by
  have hc : ((h.map F).map G).cyclesIso.hom =
      (h.map (F ⋙ G)).cyclesIso.hom := by
    apply (cancel_mono (h.map (F ⋙ G)).i).1
    change _ ≫ ((h.map F).map G).i = _
    rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
    rfl
  refine ⟨hc, ?_⟩
  apply (cancel_epi ((S.map F).map G).homologyπ).1
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, hc]
  rfl

private theorem mapHomologyIso_hom_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom := by
  let h := S.homologyData.left
  rw [(h.map F).mapHomologyIso_eq G, h.mapHomologyIso_eq F,
    h.mapHomologyIso_eq (F ⋙ G)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rw [← G.map_comp_assoc, Iso.inv_hom_id, G.map_id, Category.id_comp,
    (iteratedHomologyData_comparison S h F G).2]
  rfl

private noncomputable def homComp (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj
        ((restrict R A).obj Q)).obj F).homology i ≃+
      ((((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F).homology i) :=
  let C := ((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F
  let T := ((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj
    ((restrict R A).obj Q)).obj F
  let UA := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let UR := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  (((T.sc i).mapHomologyIso UR).symm ≪≫
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) i).mapIso
      (addComp R A Q F)).symm ≪≫
    (C.sc i).mapHomologyIso UA).addCommGroupIsoToAddEquiv

private theorem homComp_naturality (R A Aq : Type u)
    [CommRing R] [CommRing A] [CommRing Aq]
    [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (Qq : CochainComplex (ModuleCat.{u} Aq) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (g : (restrict R A).obj Q ⟶ (restrict R Aq).obj Qq)
    (v : (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ⟶
      (restrict A Aq).obj (((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F))
    (hv : ∀ (p q n : ℤ) (h : p + q = n) (x : Q.X p) (y : F.X q),
      v.f n ((HomologicalComplex.ιMapBifunctor Q F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h)
          (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y))) =
      (HomologicalComplex.ιMapBifunctor Qq F
        (ModuleCat.mixedTensor (algebraMap R Aq)) (.up ℤ) p q n h)
          ((g.f p x) ⊗ₜ[Aq] ((1 : Aq) ⊗ₜ[R,algebraMap R Aq] y))) (i : ℤ) (x) :
    (((((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F).sc i).mapHomologyIso
       (ModuleCat.restrictScalars (algebraMap A Aq))).inv
        (homComp R Aq Qq F i (HomologicalComplex.homologyMap
          (((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.map g).app F) i x)) =
      HomologicalComplex.homologyMap v i (homComp R A Q F i x) := by
  let C := ((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F
  let Cq := ((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F
  let T := (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex
  let UA := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let Uq := forget₂ (ModuleCat.{u} Aq) AddCommGrpCat
  let UR := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  let r := ModuleCat.restrictScalars (algebraMap A Aq)
  let a := addComp R A Q F
  let b := addComp R Aq Qq F
  let ha := (C.sc i).mapHomologyIso UA
  let hq := (Cq.sc i).mapHomologyIso Uq
  let hqr := (((restrict A Aq).obj Cq).sc i).mapHomologyIso UA
  let j := (Cq.sc i).mapHomologyIso r
  let t := ((T.obj ((restrict R A).obj Q)).obj F).sc i |>.mapHomologyIso UR
  let tq := ((T.obj ((restrict R Aq).obj Qq)).obj F).sc i |>.mapHomologyIso UR
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) i
  let vg := ((UA.mapHomologicalComplex (.up ℤ)).map v)
  let tg := ((UR.mapHomologicalComplex (.up ℤ)).map ((T.map g).app F))
  have hn := congrArg H.map (addComp_naturality R A Aq Q Qq F g v hv)
  simp only [Functor.map_comp] at hn
  change H.map vg ≫ H.map b.hom = H.map a.hom ≫ H.map tg at hn
  have hn' : H.map a.inv ≫ H.map vg = H.map tg ≫ H.map b.inv := by
    apply (cancel_mono (H.map b.hom)).1
    rw [Category.assoc, hn, ← H.map_comp_assoc, a.inv_hom_id, H.map_id,
      Category.id_comp, Category.assoc, ← H.map_comp, b.inv_hom_id,
      H.map_id, Category.comp_id]
  have hcomp : hqr.hom ≫ UA.map j.hom = hq.hom :=
    mapHomologyIso_hom_comp (Cq.sc i) r UA
  have hj : hq.hom ≫ UA.map j.inv = hqr.hom := by
    erw [← hcomp, Category.assoc, ← UA.map_comp, j.hom_inv_id, UA.map_id,
      Category.comp_id]
  have hvh := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map v) UA
  change H.map vg ≫ hqr.hom = ha.hom ≫ UA.map (HomologicalComplex.homologyMap v i)
    at hvh
  have hth := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map ((T.map g).app F)) UR
  change UR.map (HomologicalComplex.homologyMap ((T.map g).app F) i) ≫ tq.inv =
    t.inv ≫ H.map tg at hth
  have heq : UR.map (HomologicalComplex.homologyMap ((T.map g).app F) i) ≫ tq.inv ≫
      H.map b.inv ≫ hq.hom ≫ UA.map j.inv =
    t.inv ≫ H.map a.inv ≫ ha.hom ≫ UA.map (HomologicalComplex.homologyMap v i) := by
    erw [reassoc_of% hth, hj, ← reassoc_of% hn', hvh]
  have he := ConcreteCategory.congr_hom heq x
  exact he

private theorem homComp_scalar (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (a : A) (x) :
    homComp R A Q F i (HomologicalComplex.homologyMap
      (((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.map
        ((restrict R A).map (a • 𝟙 Q))).app F) i x) = a • homComp R A Q F i x := by
  let C := ((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F
  let T := (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex
  let UA := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let UR := forget₂ (ModuleCat.{u} R) AddCommGrpCat
  let e := addComp R A Q F
  let v := a • 𝟙 C
  let g := ((restrict R A).map (a • 𝟙 Q))
  let t := ((T.obj ((restrict R A).obj Q)).obj F).sc i |>.mapHomologyIso UR
  let h := (C.sc i).mapHomologyIso UA
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) i
  have hn : (UA.mapHomologicalComplex (.up ℤ)).map v ≫ e.hom =
      e.hom ≫ (UR.mapHomologicalComplex (.up ℤ)).map ((T.map g).app F) := by
    ext1 n
    apply mixed_underlying_ext R A Q F n
    intro p q hpq y z
    let : Module A (((restrict R A).obj C).X n) := inferInstanceAs (Module A (C.X n))
    change (totalComp R A Q F).hom.f n (a • _) =
      ((T.map g).app F).f n ((totalComp R A Q F).hom.f n _)
    have hs : a • ((HomologicalComplex.ιMapBifunctor Q F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n hpq)
          (y ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] z))) =
      (HomologicalComplex.ιMapBifunctor Q F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n hpq)
          ((a • y) ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] z)) := by
      erw [← TensorProduct.smul_tmul', map_smul]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
    rw [hs, totalComp_formula, totalComp_formula]
    let : Module R (Q.X p) := Module.compHom (Q.X p) (algebraMap R A)
    have ht := ConcreteCategory.congr_hom
      (HomologicalComplex.ι_mapBifunctorMap g (𝟙 F)
        (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q n hpq) (y ⊗ₜ[R] z)
    exact ht.symm
  have hn' := congrArg H.map hn
  simp only [Functor.map_comp] at hn'
  have hc : H.map e.inv ≫ H.map ((UA.mapHomologicalComplex (.up ℤ)).map v) =
      H.map ((UR.mapHomologicalComplex (.up ℤ)).map ((T.map g).app F)) ≫ H.map e.inv := by
    apply (cancel_mono (H.map e.hom)).1
    rw [Category.assoc, hn', ← H.map_comp_assoc, e.inv_hom_id, H.map_id,
      Category.id_comp, Category.assoc, ← H.map_comp, e.inv_hom_id,
      H.map_id, Category.comp_id]
  have hv := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map v) UA
  have hg := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map ((T.map g).app F)) UR
  change UR.map (HomologicalComplex.homologyMap ((T.map g).app F) i) ≫ t.inv =
    t.inv ≫ H.map ((UR.mapHomologicalComplex (.up ℤ)).map ((T.map g).app F)) at hg
  change H.map ((UA.mapHomologicalComplex (.up ℤ)).map v) ≫ h.hom =
    h.hom ≫ UA.map (HomologicalComplex.homologyMap v i) at hv
  have he : UR.map (HomologicalComplex.homologyMap ((T.map g).app F) i) ≫ t.inv ≫
        H.map e.inv ≫ h.hom =
      t.inv ≫ H.map e.inv ≫ h.hom ≫ UA.map (HomologicalComplex.homologyMap v i) := by
    erw [reassoc_of% hg, ← reassoc_of% hc, hv]
  have he' := ConcreteCategory.congr_hom he x
  have hs : HomologicalComplex.homologyMap v i = a • 𝟙 (C.homology i) := by
    unfold HomologicalComplex.homologyMap
    change ShortComplex.homologyMap (a • 𝟙 (C.sc i)) = _
    rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  rw [hs] at he'
  exact he'

/-- The mixed total tensor has the ordinary underlying R-tensor homology, naturally
for maps specified on diagonal pure tensors, and compatibly with first-factor scalars.
Source: Stacks Project, Tag 06Y6, ordinary balanced tensor identifications.
(blueprint: new-lem-pc-mixed-tensor-underlying-homology).

Proof: on modules the map x tensor_R y -> x tensor_A (1 tensor_R y)
is an R-linear isomorphism to the restriction of M tensor_A (A tensor_R N).
Its inverse sends x tensor_A (a tensor_R y) to (a x) tensor_R y. The balancing
relations prove that both maps are well-defined and inverse. These maps are
natural in both modules. Restriction of scalars preserves coproducts, so taking
coproducts over p+q=n gives an isomorphism of the total R-complexes. The two
summands of the signed total differential commute with this isomorphism by
module naturality, with identical signs. Apply homology and the exact restriction
homology isomorphism to obtain e. Multiplication by a on the first factor gives
the scalar equation. For the second equation, the given generator formula for v
identifies its underlying R-chain map with tensoring g by F under the chain
isomorphisms: coproduct extensionality and tensor induction suffice. Take homology
and use naturality of the restriction homology isomorphism. No K-flatness or
resolution is used here. In particular F, Q, g and v can be zero. -/
theorem exists_mixedTensorUnderlyingHomology
    (R : Type u) [CommRing R] (i : ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    let T := (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex
    ∃ e : ∀ (A : Type u) [CommRing A] [Algebra R A]
        (Q : CochainComplex (ModuleCat.{u} A) ℤ),
      (((T.obj ((restrict R A).obj Q)).obj F).homology i) ≃+
        ((((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F).homology i),
      (∀ (A : Type u) [CommRing A] [Algebra R A]
        (Q : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) x,
        e A Q (HomologicalComplex.homologyMap
          ((T.map ((restrict R A).map (a • 𝟙 Q))).app F) i x) = a • e A Q x) ∧
      (∀ (A Aq : Type u) [CommRing A] [CommRing Aq]
        [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]
        (Q : CochainComplex (ModuleCat.{u} A) ℤ)
        (Qq : CochainComplex (ModuleCat.{u} Aq) ℤ)
        (g : (restrict R A).obj Q ⟶ (restrict R Aq).obj Qq)
        (v : (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ⟶
          (restrict A Aq).obj
            (((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F)),
        (∀ (p q n : ℤ) (h : p + q = n) (x : Q.X p) (y : F.X q),
          v.f n ((HomologicalComplex.ιMapBifunctor Q F
            (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h)
              (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y))) =
          (HomologicalComplex.ιMapBifunctor Qq F
            (ModuleCat.mixedTensor (algebraMap R Aq)) (.up ℤ) p q n h)
              ((g.f p x) ⊗ₜ[Aq] ((1 : Aq) ⊗ₜ[R,algebraMap R Aq] y))) →
        ∀ x,
          (((((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F).sc i).mapHomologyIso
             (ModuleCat.restrictScalars (algebraMap A Aq))).inv
              (e Aq Qq (HomologicalComplex.homologyMap ((T.map g).app F) i x)) =
          HomologicalComplex.homologyMap v i (e A Q x)) := by
  refine ⟨fun A _ _ Q ↦ homComp R A Q F i, ?_, ?_⟩
  · intro A _ _ Q a x
    exact homComp_scalar R A Q F i a x
  · intro A Aq _ _ _ _ _ _ Q Qq g v hv x
    exact homComp_naturality R A Aq Q Qq F g v hv i x

end RingTensorCohomology
