/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.NormalizedHomComplexGlobalCochains
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Ordinary global cohomology of a sheaf Hom complex

Source: Stacks Project, Tag 0A8Z and the global computation in Tag 08JA.
(blueprint: lem-pur-hom-complex-global-homotopy)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace CategoryTheory

open CochainComplex HomComplex Limits Preadditive in
private noncomputable def globalBifunctor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)ᵒᵖ ×
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
          CochainComplex AddCommGrpCat.{u} ℤ :=
  Functor.uncurry.obj (homComplexFunctor.{u, u, u, u} (R := R)) ⋙
    (preadditiveCoyoneda.obj (op (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))).mapHomologicalComplex
        (.up ℤ)

open CochainComplex HomComplex Limits Preadditive in
private noncomputable def globalComplexIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (X : (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)ᵒᵖ ×
        CochainComplex (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    (globalBifunctor R).obj X ≅ HomComplex X.1.unop X.2 := by
  dsimp only [globalBifunctor, Functor.comp_obj, Functor.uncurry_obj_obj]
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (normalizedHomGlobalCochains R X.1.unop X.2 n).toAddCommGrpIso) (by
      intro i j hij
      ext s
      exact (normalizedHomGlobalCochains_comm R X.1.unop X.2 i j s).symm)

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex Limits Preadditive in
private def externalMap
    {D : Type*} [Category* D] [Preadditive D]
    {A A' B B' : CochainComplex D ℤ} (f : A' ⟶ A) (g : B ⟶ B') :
    HomComplex A B ⟶ HomComplex A' B' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun a ↦ ((Cochain.ofHom f).comp a (zero_add n)).comp
        (Cochain.ofHom g) (add_zero n)
      map_zero' := by simp
      map_add' := by intros; simp }
  comm' i j _ := by
    ext a
    change δ i j (((Cochain.ofHom f).comp a (zero_add i)).comp
      (Cochain.ofHom g) (add_zero i)) =
        ((Cochain.ofHom f).comp (δ i j a) (zero_add j)).comp
          (Cochain.ofHom g) (add_zero j)
    rw [δ_comp_ofHom, δ_ofHom_comp]

open CochainComplex HomComplex Limits Preadditive in
private lemma externalMap_v
    {D : Type*} [Category* D] [Preadditive D]
    {A A' B B' : CochainComplex D ℤ} (f : A' ⟶ A) (g : B ⟶ B')
    (n : ℤ) (a : Cochain A B n) (p q : ℤ) (hpq : p + n = q) :
    ((externalMap f g).f n a).v p q hpq = f.f p ≫ a.v p q hpq ≫ g.f q := by
  change (((Cochain.ofHom f).comp a (zero_add n)).comp
    (Cochain.ofHom g) (add_zero n)).v p q hpq = _
  simp [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v]

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex Limits Preadditive in
private lemma globalComplexIso_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    {A A' B B' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : A' ⟶ A) (g : B ⟶ B') :
    (globalBifunctor R).map (f.op, g) ≫ (globalComplexIso R (op A', B')).hom =
      (globalComplexIso R (op A, B)).hom ≫ externalMap f g := by
  ext n s
  change (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      (((homComplexFunctor.{u, u, u, u} (R := R)).obj (op A)).obj B).X n) at s
  apply Cochain.ext
  intro p q hpq
  change (normalizedHomGlobalCochains R A' B' n
    (s ≫ ((((homComplexFunctor.{u, u, u, u} (R := R)).map f.op).app B ≫
      ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op A')).map g).f n))).v p q hpq =
    ((externalMap f g).f n (normalizedHomGlobalCochains R A B n s)).v p q hpq
  rw [normalizedHomGlobalCochains_v, Category.assoc]
  have hm :
      (((homComplexFunctor.{u, u, u, u} (R := R)).map f.op).app B ≫
        ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op A')).map g).f n ≫
          normalizedHomProjection (R := R) A' B' n p q hpq =
      normalizedHomProjection (R := R) A B n p q hpq ≫
        SheafOfModules.homObjMap (R := R) (f.f p) (g.f q) := by
    exact (Classical.choose_spec
      (homComplex_projections_exists.{u, u, u, u} (J := J) (R := R))).2.2
        A A' B B' f g n p q hpq
  rw [hm]
  rw [← Category.assoc, normalizedHomFactorEquiv_comp]
  exact (externalMap_v f g n (normalizedHomGlobalCochains R A B n s) p q hpq).symm

open CochainComplex HomComplex Limits Preadditive in
private noncomputable def zeroClassEquiv
    {D : Type*} [Category* D] [Preadditive D] (A B : CochainComplex D ℤ) :
    CohomologyClass A B 0 ≃+
      ((HomotopyCategory.quotient D (.up ℤ)).obj A ⟶
        (HomotopyCategory.quotient D (.up ℤ)).obj B) :=
  (CohomologyClass.homAddEquiv (K := A) (L := B) (n := 0)).trans
    (Linear.homCongr ℤ (Iso.refl _)
      ((HomotopyCategory.quotient D (.up ℤ)).mapIso
        ((shiftFunctorZero _ ℤ).app B))).toAddEquiv

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex Limits Preadditive in
private lemma zeroClassEquiv_mk
    {D : Type*} [Category* D] [Preadditive D]
    {A B : CochainComplex D ℤ} (z : Cocycle A B 0) :
    zeroClassEquiv A B (CohomologyClass.mk z) =
      (HomotopyCategory.quotient D (.up ℤ)).map z.homOf := by
  change (𝟙 _ ≫ (HomotopyCategory.quotient D (.up ℤ)).map
    (Cocycle.equivHomShift.symm z)) ≫
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((shiftFunctorZero _ ℤ).hom.app B) = _
  rw [Category.id_comp, ← Functor.map_comp]
  congr 1
  ext p
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cocycle.rightShift,
    Cochain.rightShift_v, CochainComplex.shiftFunctorZero_hom_app_f]

open CochainComplex HomComplex Limits Preadditive in
private noncomputable def externalHomologyIso
    {D : Type*} [Category* D] [Preadditive D] (A B : CochainComplex D ℤ) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).obj
        (HomComplex A B) ≅ AddCommGrpCat.of
      ((HomotopyCategory.quotient D (.up ℤ)).obj A ⟶
        (HomotopyCategory.quotient D (.up ℤ)).obj B) :=
  (HomComplex.leftHomologyData A B 0).homologyIso ≪≫
    (zeroClassEquiv A B).toAddCommGrpIso

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex Limits Preadditive in
private noncomputable def externalHomologyMapData
    {D : Type*} [Category* D] [Preadditive D]
    {A A' B B' : CochainComplex D ℤ} (f : A' ⟶ A) (g : B ⟶ B') :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ 0).map (externalMap f g))
      (HomComplex.leftHomologyData A B 0) (HomComplex.leftHomologyData A' B' 0) where
  φK := AddCommGrpCat.ofHom
    { toFun := fun z ↦ (z.precomp f).postcomp g
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  φH := (zeroClassEquiv A B).toAddCommGrpIso.hom ≫
    (AddCommGrpCat.ofHom
      { toFun := fun a ↦ (HomotopyCategory.quotient D (.up ℤ)).map f ≫ a ≫
          (HomotopyCategory.quotient D (.up ℤ)).map g
        map_zero' := by simp
        map_add' := by intros; simp [comp_add, add_comp] }) ≫
      (zeroClassEquiv A' B').toAddCommGrpIso.inv
  commi := by ext z; rfl
  commf' := by
    rw [← cancel_mono (HomComplex.leftHomologyData A' B' 0).i]
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    have hi : AddCommGrpCat.ofHom
        { toFun := fun z : Cocycle A B 0 ↦ (z.precomp f).postcomp g
          map_zero' := by ext; simp
          map_add' := by intros; ext; simp } ≫
        (HomComplex.leftHomologyData A' B' 0).i =
      (HomComplex.leftHomologyData A B 0).i ≫ (externalMap f g).f 0 := by
      ext z
      rfl
    rw [hi, ShortComplex.LeftHomologyData.f'_i_assoc]
    exact ((HomologicalComplex.shortComplexFunctor _ _ 0).map
      (externalMap f g)).comm₁₂.symm
  commπ := by
    ext z
    apply (zeroClassEquiv A' B').injective
    change zeroClassEquiv A' B' ((zeroClassEquiv A' B').symm
      ((HomotopyCategory.quotient D (.up ℤ)).map f ≫
        zeroClassEquiv A B (CohomologyClass.mk z) ≫
          (HomotopyCategory.quotient D (.up ℤ)).map g)) =
      zeroClassEquiv A' B' (CohomologyClass.mk ((z.precomp f).postcomp g))
    rw [AddEquiv.apply_symm_apply, zeroClassEquiv_mk, zeroClassEquiv_mk,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext p
    simp [Cocycle.homOf, Cocycle.precomp, Cocycle.postcomp,
      Cochain.comp_zero_cochain_v]

set_option backward.isDefEq.respectTransparency false in
open CochainComplex HomComplex Limits Preadditive in
private lemma externalHomologyIso_naturality
    {D : Type*} [Category* D] [Preadditive D]
    {A A' B B' : CochainComplex D ℤ} (f : A' ⟶ A) (g : B ⟶ B') :
    HomologicalComplex.homologyMap (externalMap f g) 0 ≫
      (externalHomologyIso A' B').hom =
    (externalHomologyIso A B).hom ≫ AddCommGrpCat.ofHom
      { toFun := fun a ↦ (HomotopyCategory.quotient D (.up ℤ)).map f ≫ a ≫
          (HomotopyCategory.quotient D (.up ℤ)).map g
        map_zero' := by simp
        map_add' := by intros; simp [comp_add, add_comp] } := by
  have h := (externalHomologyMapData f g).homologyMap_eq
  change HomologicalComplex.homologyMap (externalMap f g) 0 = _ at h
  rw [h]
  dsimp only [externalHomologyIso, externalHomologyMapData]
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  ext a
  change zeroClassEquiv A' B' ((zeroClassEquiv A' B').symm
    ((HomotopyCategory.quotient D (.up ℤ)).map f ≫
      zeroClassEquiv A B ((HomComplex.leftHomologyData A B 0).homologyIso.hom a) ≫
        (HomotopyCategory.quotient D (.up ℤ)).map g)) = _
  exact AddEquiv.apply_symm_apply _ _

-- The natural-isomorphism assembly checks several large chosen-functor interfaces.
set_option backward.isDefEq.respectTransparency false in
/-- Ordinary zeroth cohomology of global cochains is naturally the group of homotopy classes.
Source: Stacks Project, Tag 0A8Z and Tag 08JA, first global-cochain computation.
(blueprint: lem-pur-hom-complex-global-homotopy)

Proof: take the projections furnished by `homComplex_projections_exists` once for the
whole bifunctor. Their product universal property identifies maps from the unit to
Hom(L,M)^n with families L^p → M^(p+n), additively. The differential formula identifies
this with the external Hom differential, as in `homComplex_global_cochains`. The map
formula for these same projections proves naturality under both precomposition and
postcomposition. Pass to degree-zero homology. The external Hom-complex homology
comparison identifies its elements with cocycles modulo coboundaries. Degree-zero
cocycles are chain maps, and coboundaries are precisely maps homotopic to zero.
`CohomologyClass.homAddEquiv` at zero, followed by the shift-zero isomorphism,
therefore identifies this group with morphisms in the homotopy category. On chain-map
representatives all three comparisons send pre- and postcomposition to composition;
surjectivity of the cocycle quotient proves naturality on homology. Assemble these
additive isomorphisms with `NatIso.ofComponents`. This calculation uses no K-flatness,
K-injectivity or boundedness, and applies to zero complexes as well. -/
theorem homComplex_global_homotopy
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
    let Γ := preadditiveCoyoneda.obj (op (SheafOfModules.unit R₀))
    let q := HomotopyCategory.quotient (SheafOfModules.{u} R₀) (ComplexShape.up ℤ)
    Nonempty ((Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        Γ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0) ≅
      q.op.prod q ⋙ Functor.uncurry.obj preadditiveCoyoneda) := by
  dsimp only
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (.up ℤ)
  let e : globalBifunctor R ⋙ H ≅
      q.op.prod q ⋙ Functor.uncurry.obj preadditiveCoyoneda :=
    NatIso.ofComponents
      (fun X ↦ H.mapIso (globalComplexIso R X) ≪≫
        externalHomologyIso X.1.unop X.2) (by
      intro X Y f
      have h := H.congr_map (globalComplexIso_naturality R f.1.unop f.2)
      simp only [Functor.map_comp] at h
      change H.map ((globalBifunctor R).map f) ≫
        H.map (globalComplexIso R Y).hom =
          H.map (globalComplexIso R X).hom ≫ H.map (externalMap f.1.unop f.2) at h
      dsimp only [H, q] at h ⊢
      simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      rw [← Category.assoc, h, Category.assoc]
      change H.map (globalComplexIso R X).hom ≫
          HomologicalComplex.homologyMap (externalMap f.1.unop f.2) 0 ≫
            (externalHomologyIso Y.1.unop Y.2).hom = _
      rw [externalHomologyIso_naturality]
      ext a
      change (q.map f.1.unop ≫ _ ≫ q.map f.2) = _
      exact (Category.assoc _ _ _).symm)
  dsimp only [globalBifunctor] at e
  exact ⟨(Functor.associator _ _ _).symm ≪≫ e⟩

end CategoryTheory
