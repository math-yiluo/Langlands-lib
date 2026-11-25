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
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Ordinary global Hom-complex cohomology with independent site universes

Source: Stacks Project, Equation 0A8Z and Lemma 08JA.
(blueprint: lem-pur-hom-complex-global-homotopy)
-/

@[expose] public section

set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
namespace CategoryTheory

attribute [local irreducible] homComplexFunctor
set_option backward.isDefEq.respectTransparency true

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{max c v r}}

set_option hygiene false in
local notation "𝓡" =>
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R
set_option hygiene false in
local notation "Mod" => SheafOfModules.{max c v r} 𝓡

private noncomputable def rhomNormalizedHomFactorEquiv (M N : Mod) :
    (SheafOfModules.unit 𝓡 ⟶ SheafOfModules.homObj (R := R) M N) ≃+ (M ⟶ N) where
  toEquiv := (SheafOfModules.unitHomEquiv _).trans
    (SheafOfModules.homObjSectionsEquiv M N)
  map_add' f g := by rfl

private lemma rhomNormalizedHomFactorEquiv_comp {M M' N N' : Mod}
    (s : SheafOfModules.unit 𝓡 ⟶ SheafOfModules.homObj (R := R) M N)
    (f : M' ⟶ M) (g : N ⟶ N') :
    rhomNormalizedHomFactorEquiv.{c, v, r} M' N' (s ≫ SheafOfModules.homObjMap (R := R) f g) =
      f ≫ rhomNormalizedHomFactorEquiv.{c, v, r} M N s ≫ g := by
  rfl

attribute [local irreducible] rhomNormalizedHomFactorEquiv

/-- Construct the global-cochain comparison from a specified product cone.
The inverse is the unique lift to that product. -/
private noncomputable def rhomNormalizedHomGlobalCochainsOfFan (A B : CochainComplex Mod ℤ) (n : ℤ)
    (Z : Mod) (π : ∀ p q : ℤ, p + n = q → (Z ⟶
      SheafOfModules.homObj (R := R) (A.X p) (B.X q)))
    (hπ : IsLimit (Fan.mk Z (fun p ↦ π p (p + n) rfl))) :
    (SheafOfModules.unit 𝓡 ⟶ Z) ≃+ CochainComplex.HomComplex.Cochain A B n :=
    { toFun s := CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
        rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X q) (s ≫ π p q hpq)
      invFun c := Fan.IsLimit.lift hπ fun p ↦
        (rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)
      left_inv s := by
        apply Fan.IsLimit.hom_ext hπ
        intro p
        simpa using Fan.IsLimit.fac hπ (fun p ↦
          s ≫ π p (p + n) rfl) p
      right_inv c := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        subst q
        change rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + n))
          (Fan.IsLimit.lift hπ (fun p ↦
            (rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + n))).symm
              (c.v p (p + n) rfl)) ≫
            π p (p + n) rfl) = c.v p (p + n) rfl
        have hf := Fan.IsLimit.fac hπ (fun p ↦
          (rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + n))).symm (c.v p (p + n) rfl)) p
        simp only [fan_mk_proj] at hf
        rw [hf]
        exact AddEquiv.apply_symm_apply _ _
      map_add' s t := by
        apply CochainComplex.HomComplex.Cochain.ext
        intro p q hpq
        simp [add_comp] }

private lemma rhomNormalizedHomGlobalCochainsOfFan_v (A B : CochainComplex Mod ℤ) (n : ℤ)
    (Z : Mod) (π : ∀ p q : ℤ, p + n = q → (Z ⟶
      SheafOfModules.homObj (R := R) (A.X p) (B.X q)))
    (hπ : IsLimit (Fan.mk Z (fun p ↦ π p (p + n) rfl)))
    (s : SheafOfModules.unit 𝓡 ⟶ Z) (p q : ℤ) (h : p + n = q) :
    (rhomNormalizedHomGlobalCochainsOfFan.{c, v, r} A B n Z π hπ s).v p q h =
      rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X q) (s ≫ π p q h) := rfl

attribute [local irreducible] rhomNormalizedHomGlobalCochainsOfFan

/-- The projections exposed by the Hom-complex product specification. -/
private noncomputable def rhomNormalizedHomProjection (A B : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex (R := R) A B).X n ⟶ SheafOfModules.homObj (R := R) (A.X p) (B.X q) :=
  homComplexπ.{c, v, max c v r, max c v r} (J := J) (R := R) A B n p q h

/-- The canonical product projections of the chosen Hom complex form a limit cone. -/
private theorem rhomNormalizedHomProjection_isLimit (A B : CochainComplex Mod ℤ) (n : ℤ) :
    Nonempty (IsLimit (Fan.mk ((homComplex (R := R) A B).X n)
      (fun p ↦ rhomNormalizedHomProjection.{c, v, r} (R := R) A B n p (p + n) rfl))) := by
  exact ⟨homComplexIsLimit.{c, v, max c v r, max c v r} (R := R) A B n⟩

/-- The explicit product-projection comparison with ordinary cochains.
Source: Stacks Project, sites-cohomology.tex, Tag 0A8Z.
(blueprint: lem-pc-normalized-hom-complex-global-cochains). -/
private noncomputable def rhomNormalizedHomGlobalCochains
    (R : Sheaf J CommRingCat.{max c v r}) (A B : CochainComplex Mod ℤ) (n : ℤ) :
    (SheafOfModules.unit 𝓡 ⟶ (homComplex (R := R) A B).X n) ≃+
      CochainComplex.HomComplex.Cochain A B n :=
  rhomNormalizedHomGlobalCochainsOfFan.{c, v, r} A B n _
    (rhomNormalizedHomProjection.{c, v, r} (R := R) A B n)
    (rhomNormalizedHomProjection_isLimit.{c, v, r} A B n).some

/-- The component formula retained by the explicit comparison.
Source: Stacks Project, sites-cohomology.tex, Tag 0A8Z.
(blueprint: lem-pc-normalized-hom-complex-global-cochains). -/
private theorem rhomNormalizedHomGlobalCochains_v
    (R : Sheaf J CommRingCat.{max c v r}) (A B : CochainComplex Mod ℤ) (n : ℤ)
    (s : SheafOfModules.unit 𝓡 ⟶ (homComplex (R := R) A B).X n)
    (p q : ℤ) (h : p + n = q) :
    (rhomNormalizedHomGlobalCochains.{c, v, r} R A B n s).v p q h =
      rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X q)
        (s ≫ rhomNormalizedHomProjection.{c, v, r} (R := R) A B n p q h) :=
  rhomNormalizedHomGlobalCochainsOfFan_v.{c, v, r} A B n _ _ _ s p q h

set_option backward.isDefEq.respectTransparency false in
/-- Differential compatibility of the comparison built from two product cones. -/
private lemma rhomNormalizedHomGlobalCochainsOfFan_comm (A B : CochainComplex Mod ℤ)
    (i j : ℤ) (hij : i + 1 = j) (Zi Zj : Mod)
    (πi : ∀ p q : ℤ, p + i = q → (Zi ⟶
      SheafOfModules.homObj (R := R) (A.X p) (B.X q)))
    (πj : ∀ p q : ℤ, p + j = q → (Zj ⟶
      SheafOfModules.homObj (R := R) (A.X p) (B.X q)))
    (hi : IsLimit (Fan.mk Zi (fun p ↦ πi p (p + i) rfl)))
    (hj : IsLimit (Fan.mk Zj (fun p ↦ πj p (p + j) rfl))) (d : Zi ⟶ Zj)
    (hd : ∀ (p q q' p' : ℤ) (hpq : p + j = q) (hq' : p + i = q')
      (hp' : p' + i = q), d ≫ πj p q hpq =
        πi p q' hq' ≫ SheafOfModules.homObjMap (R := R) (𝟙 (A.X p)) (B.d q' q) -
          i.negOnePow • (πi p' q hp' ≫
            SheafOfModules.homObjMap (R := R) (A.d p p') (𝟙 (B.X q))))
    (s : SheafOfModules.unit 𝓡 ⟶ Zi) :
    rhomNormalizedHomGlobalCochainsOfFan.{c, v, r} A B j Zj πj hj (s ≫ d) =
      CochainComplex.HomComplex.δ i j
        (rhomNormalizedHomGlobalCochainsOfFan.{c, v, r} A B i Zi πi hi s) := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  rw [CochainComplex.HomComplex.δ_v i j hij _ p q hpq (p + i) (p + 1)
    (by omega) rfl]
  rw [rhomNormalizedHomGlobalCochainsOfFan_v.{c, v, r},
    rhomNormalizedHomGlobalCochainsOfFan_v.{c, v, r},
    rhomNormalizedHomGlobalCochainsOfFan_v.{c, v, r}]
  rw [Category.assoc, hd p q (p + i) (p + 1) hpq rfl (by omega)]
  simp only [comp_sub, Units.smul_def, comp_zsmul, ← Category.assoc,
    map_sub, map_zsmul, rhomNormalizedHomFactorEquiv_comp.{c, v, r},
    Category.id_comp, Category.comp_id]
  change rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + i))
      (s ≫ πi p (p + i) rfl) ≫ B.d (p + i) q -
        (i.negOnePow : ℤˣ) • (A.d p (p + 1) ≫
          rhomNormalizedHomFactorEquiv.{c, v, r} (A.X (p + 1)) (B.X q)
            (s ≫ πi (p + 1) q (by omega))) =
    rhomNormalizedHomFactorEquiv.{c, v, r} (A.X p) (B.X (p + i))
      (s ≫ πi p (p + i) rfl) ≫ B.d (p + i) q +
        j.negOnePow • A.d p (p + 1) ≫
          rhomNormalizedHomFactorEquiv.{c, v, r} (A.X (p + 1)) (B.X q)
            (s ≫ πi (p + 1) q (by omega))
  subst j
  simp only [Int.negOnePow_succ, Units.smul_def, Units.val_neg,
    neg_smul, sub_eq_add_neg]

/-- The explicit normalized comparison commutes with the cochain differential.
Source: Stacks Project, sites-cohomology.tex, Tag 0A8Z.
(blueprint: lem-pc-normalized-hom-complex-global-cochains).
Proof: project onto each Hom factor, apply the differential projection formula,
and identify internal-Hom sections with morphisms. The resulting formula is
exactly the ordinary cochain differential. For nonconsecutive degrees both
sides vanish by the complex shape. -/
private theorem rhomNormalizedHomGlobalCochains_comm
    (R : Sheaf J CommRingCat.{max c v r}) (A B : CochainComplex Mod ℤ)
    (i j : ℤ) (s : SheafOfModules.unit 𝓡 ⟶ (homComplex (R := R) A B).X i) :
    rhomNormalizedHomGlobalCochains.{c, v, r} R A B j (s ≫ (homComplex (R := R) A B).d i j) =
      CochainComplex.HomComplex.δ i j (rhomNormalizedHomGlobalCochains.{c, v, r} R A B i s) := by
  classical
  by_cases hij : i + 1 = j
  · exact rhomNormalizedHomGlobalCochainsOfFan_comm.{c, v, r} A B i j hij
      ((homComplex (R := R) A B).X i) ((homComplex (R := R) A B).X j)
      (rhomNormalizedHomProjection.{c, v, r} (R := R) A B i)
      (rhomNormalizedHomProjection.{c, v, r} (R := R) A B j)
      (rhomNormalizedHomProjection_isLimit.{c, v, r} A B i).some
      (rhomNormalizedHomProjection_isLimit.{c, v, r} A B j).some
      ((homComplex (R := R) A B).d i j)
      (fun p q q' p' hpq hq' hp' ↦
        homComplex_d_π.{c, v, max c v r, max c v r} (R := R)
          A B i j p q q' p' hij hpq hq' hp') s
  · rw [(homComplex (R := R) A B).shape i j
        (by simpa [ComplexShape.up_Rel] using hij), comp_zero, map_zero,
        CochainComplex.HomComplex.δ_shape i j hij]

open CochainComplex HomComplex Limits Preadditive in
private noncomputable def globalBifunctor
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r}) :
    (CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)ᵒᵖ ×
      CochainComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
          CochainComplex AddCommGrpCat.{max c v r} ℤ :=
  let Γ := preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
  Functor.uncurry.obj (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙
    Γ.mapHomologicalComplex (.up ℤ)

open CochainComplex HomComplex Limits Preadditive in
private noncomputable def globalComplexIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r})
    (X : (CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)ᵒᵖ ×
        CochainComplex (SheafOfModules.{max c v r}
          ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    (globalBifunctor.{c, v, r} R).obj X ≅ HomComplex X.1.unop X.2 := by
  dsimp only [globalBifunctor, Functor.comp_obj, Functor.uncurry_obj_obj]
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (rhomNormalizedHomGlobalCochains.{c, v, r} R X.1.unop X.2 n).toAddCommGrpIso) (by
      intro i j hij
      ext s
      exact (rhomNormalizedHomGlobalCochains_comm.{c, v, r} R X.1.unop X.2 i j s).symm)

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
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max c v r})
    {A A' B B' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (f : A' ⟶ A) (g : B ⟶ B') :
    (globalBifunctor.{c, v, r} R).map (f.op, g) ≫ (globalComplexIso.{c, v, r} R (op A', B')).hom =
      (globalComplexIso.{c, v, r} R (op A, B)).hom ≫ externalMap f g := by
  ext n s
  change (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⟶
      (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).obj B).X n) at s
  apply Cochain.ext
  intro p q hpq
  change (rhomNormalizedHomGlobalCochains.{c, v, r} R A' B' n
    (s ≫ ((((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map f.op).app B ≫
      ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj
        (op A')).map g).f n))).v p q hpq =
    ((externalMap f g).f n (rhomNormalizedHomGlobalCochains.{c, v, r} R A B n s)).v p q hpq
  rw [rhomNormalizedHomGlobalCochains_v.{c, v, r}, Category.assoc]
  have hm :
      (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map f.op).app B ≫
        ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A')).map g).f n ≫
          rhomNormalizedHomProjection.{c, v, r} (R := R) A' B' n p q hpq =
      rhomNormalizedHomProjection.{c, v, r} (R := R) A B n p q hpq ≫
        SheafOfModules.homObjMap (R := R) (f.f p) (g.f q) := by
    exact homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} (R := R)
      f g n p q hpq
  rw [hm]
  rw [← Category.assoc, rhomNormalizedHomFactorEquiv_comp.{c, v, r}]
  rw [← rhomNormalizedHomGlobalCochains_v.{c, v, r}]
  exact (externalMap_v f g n
    (rhomNormalizedHomGlobalCochains.{c, v, r} R A B n s) p q hpq).symm

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
theorem homComplex_global_homotopyOfUniverses
    {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r}) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R
    let Γ := preadditiveCoyoneda.obj (op (SheafOfModules.unit R₀))
    let q := HomotopyCategory.quotient (SheafOfModules.{max c v r} R₀) (ComplexShape.up ℤ)
    Nonempty ((Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        Γ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v r} (ComplexShape.up ℤ) 0) ≅
      q.op.prod q ⋙ Functor.uncurry.obj preadditiveCoyoneda) := by
  dsimp only
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v r} (.up ℤ) 0
  let q := HomotopyCategory.quotient
    (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) (.up ℤ)
  let e : globalBifunctor.{c, v, r} R ⋙ H ≅
      q.op.prod q ⋙ Functor.uncurry.obj preadditiveCoyoneda :=
    NatIso.ofComponents
      (fun X ↦ H.mapIso (globalComplexIso.{c, v, r} R X) ≪≫
        externalHomologyIso X.1.unop X.2) (by
      intro X Y f
      have h := H.congr_map (globalComplexIso_naturality.{c, v, r} R f.1.unop f.2)
      simp only [Functor.map_comp] at h
      change H.map ((globalBifunctor.{c, v, r} R).map f) ≫
        H.map (globalComplexIso.{c, v, r} R Y).hom =
          H.map (globalComplexIso.{c, v, r} R X).hom ≫ H.map (externalMap f.1.unop f.2) at h
      dsimp only [H, q] at h ⊢
      simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      rw [← Category.assoc, h, Category.assoc]
      change H.map (globalComplexIso.{c, v, r} R X).hom ≫
          HomologicalComplex.homologyMap (externalMap f.1.unop f.2) 0 ≫
            (externalHomologyIso Y.1.unop Y.2).hom = _
      rw [externalHomologyIso_naturality]
      ext a
      change (q.map f.1.unop ≫ _ ≫ q.map f.2) = _
      exact (Category.assoc _ _ _).symm)
  dsimp only [globalBifunctor] at e
  exact ⟨(Functor.associator _ _ _).symm ≪≫ e⟩

end CategoryTheory
