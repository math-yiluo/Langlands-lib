/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.SixFunctors.SfbHomFilteredColimit.DerivedInternalHomFilteredColimitData
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.HomComplexComponents

/-! # Signed ordinary biduality and the two augmentation comparisons

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X, 0A92 and 0A97
(blueprint: lem-sfb-ringed-signed-bidual-localization).

The statement uses only the prerequisite product Hom complex, coefficient unit,
fixed augmentation and localization factorization. It gives a family of actual chain
maps with uniqueness, zero product components, naturality, and the localization equation.
The comparison isomorphisms are fixed by their displayed homs.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

private abbrev Mod := RingedTensorModules.{c, v, u} J R

private abbrev CX := CochainComplex (Mod.{c, v, u} J R) ℤ

private noncomputable def flipEval (A B : Mod.{c, v, u} J R) :
    A ⟶ SheafOfModules.homObj (R := R) (SheafOfModules.homObj (R := R) A B) B where
  val := IsoTensorHom.tensorHomCurry.{c, v, u}
    ((β_ (PresheafOfModules.homObj A.val B.val) A.val).hom ≫
      IsoTensorHom.tensorHomUncurry.{c, v, u} (𝟙 _))

private noncomputable def betaTerm (E O : CX.{c, v, u} J R) (a : ℤ) :
    E.X a ⟶ (homComplex (R := R) (homComplex (R := R) E O) O).X a :=
  (homComplexIsLimit (R := R) (homComplex (R := R) E O) O a).lift
    (Fan.mk (E.X a) (fun q : ℤ ↦ (a * q).negOnePow •
      (flipEval.{c, v, u} J R (E.X a) (O.X (q + a)) ≫
        SheafOfModules.homObjMap (R := R)
          (homComplexπ (R := R) E O q a (q + a) (add_comm a q)) (𝟙 _))))

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma betaTerm_proj (E O : CX.{c, v, u} J R) (a q k : ℤ) (h : q + a = k) :
    betaTerm.{c, v, u} J R E O a ≫ homComplexπ (R := R) (homComplex (R := R) E O) O a q k h =
      (a * q).negOnePow • (flipEval.{c, v, u} J R (E.X a) (O.X k) ≫
        SheafOfModules.homObjMap (R := R) (homComplexπ (R := R) E O q a k (by omega)) (𝟙 _)) := by
  subst k
  exact (homComplexIsLimit (R := R) (homComplex (R := R) E O) O a).fac _ ⟨q⟩

private noncomputable def evalAt (A B : Mod.{c, v, u} J R) (U : Cᵒᵖ)
    (W : (Over U.unop)ᵒᵖ) (x : A.val.obj (op W.unop.left)) :
    (SheafOfModules.homObj (R := R) A B).val.obj U →+ B.val.obj (op W.unop.left) where
  toFun φ := (φ.app W).hom x
  map_zero' := rfl
  map_add' _ _ := rfl

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma sectionUnits {A B : Mod.{c, v, u} J R} (f : A ⟶ B)
    (e : ℤˣ) (U : Cᵒᵖ) (s : A.val.obj U) :
    ((e • f).val.app U).hom s = e • (f.val.app U).hom s := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max c v u}
    RingCat.{max c v u})).obj R
  let V := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj U
  change (V.map (e • f)).hom s = _
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_zsmul,
    LinearMap.smul_apply]
  rfl

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma sectionSubUnits {A B : Mod.{c, v, u} J R} (f g : A ⟶ B)
    (e : ℤˣ) (U : Cᵒᵖ) (s : A.val.obj U) :
    ((f - e • g).val.app U).hom s =
      (f.val.app U).hom s - e • (g.val.app U).hom s := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max c v u}
    RingCat.{max c v u})).obj R
  let V := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj U
  change (V.map (f - e • g)).hom s = _
  rw [Functor.map_sub]
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
    ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
  rfl

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma betaTerm_apply (E O : CX.{c, v, u} J R) (a q k : ℤ)
    (h : q + a = k) (U : Cᵒᵖ) (x : (E.X a).val.obj U)
    (W : (Over U.unop)ᵒᵖ)
    (φ : ((homComplex (R := R) E O).X q).val.obj (op W.unop.left)) :
    (((homComplexπ (R := R) (homComplex (R := R) E O) O a q k h).val.app U
      ((betaTerm.{c, v, u} J R E O a).val.app U x)).app W).hom φ =
      (a * q).negOnePow •
        (((homComplexπ (R := R) E O q a k (by omega)).val.app
          (op W.unop.left) φ).app (op (Over.mk (𝟙 W.unop.left)))).hom
            ((E.X a).val.map W.unop.hom.op x) := by
  have he := congrArg (fun t ↦ (evalAt.{c, v, u} J R
    ((homComplex (R := R) E O).X q) (O.X k) U W φ) (t.val.app U x))
      (betaTerm_proj.{c, v, u} J R E O a q k h)
  rw [sectionUnits.{c, v, u} J R] at he
  change _ = (evalAt.{c, v, u} J R _ _ U W φ)
    ((a * q).negOnePow • _) at he
  simp only [Units.smul_def, map_zsmul] at he
  with_unfolding_all exact he

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma homExt {X A B : Mod.{c, v, u} J R}
    (f g : X ⟶ SheafOfModules.homObj (R := R) A B)
    (h : ∀ (U : Cᵒᵖ) (x : X.val.obj U) (W : (Over U.unop)ᵒᵖ)
      (y : A.val.obj (op W.unop.left)),
      ((f.val.app U x).app W).hom y = ((g.val.app U x).app W).hom y) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h U x W)

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma differential_apply (A B : CX.{c, v, u} J R)
    (n p q q' p' : ℤ) (hpq : p + (n + 1) = q)
    (hq' : p + n = q') (hp' : p' + n = q)
    (U : Cᵒᵖ) (s : ((homComplex (R := R) A B).X n).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (A.X p).val.obj (op W.unop.left)) :
    (((homComplexπ (R := R) A B (n + 1) p q hpq).val.app U
      (((homComplex (R := R) A B).d n (n + 1)).val.app U s)).app W).hom x =
    (B.d q' q).val.app (op W.unop.left)
      ((((homComplexπ (R := R) A B n p q' hq').val.app U s).app W).hom x) -
    n.negOnePow • (show (B.X q).val.obj (op W.unop.left) from
      (((homComplexπ (R := R) A B n p' q hp').val.app U s).app W).hom
        ((A.d p p').val.app (op W.unop.left) x)) := by
  have he := congrArg (fun t ↦ (evalAt.{c, v, u} J R (A.X p) (B.X q) U W x)
    (t.val.app U s))
    (homComplex_d_π (R := R) A B n (n + 1) p q q' p' rfl hpq hq' hp')
  rw [sectionSubUnits.{c, v, u} J R] at he
  simp only [map_sub, Units.smul_def, map_zsmul] at he
  with_unfolding_all exact he

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma homPost_apply (E O O' : CX.{c, v, u} J R) (f : O ⟶ O')
    (n a b : ℤ) (h : a + n = b) (U : Cᵒᵖ)
    (φ : ((homComplex (R := R) E O).X n).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (E.X a).val.obj (op W.unop.left)) :
    (((homComplexπ (R := R) E O' n a b h).val.app U
      (((homComplexFunctor (R := R)).obj (op E)).map f |>.f n |>.val.app U φ)).app W).hom x =
    (f.f b).val.app (op W.unop.left)
      ((((homComplexπ (R := R) E O n a b h).val.app U φ).app W).hom x) := by
  have he := congrArg (fun t ↦ (evalAt.{c, v, u} J R (E.X a) (O'.X b) U W x)
    (t.val.app U φ)) (homComplexFunctor_obj_map_f_π (R := R) f n a b h)
  with_unfolding_all exact he

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma restriction_id (A : Mod.{c, v, u} J R) (U : Cᵒᵖ) (x : A.val.obj U) :
    A.val.map (𝟙 U) x = x := by
  rw [PresheafOfModules.map_id]
  rfl

attribute [local irreducible] homComplexFunctor

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma betaTerm_comm (E O : CX.{c, v, u} J R) (a : ℤ) :
    E.d a (a + 1) ≫ betaTerm.{c, v, u} J R E O (a + 1) =
      betaTerm.{c, v, u} J R E O a ≫
        (homComplex (R := R) (homComplex (R := R) E O) O).d a (a + 1) := by
  apply homComplex_hom_ext
  intro q k h
  apply homExt.{c, v, u} J R
  intro U x W φ
  change
    (((homComplexπ (R := R) (homComplex (R := R) E O) O (a + 1) q k h).val.app U
      ((betaTerm.{c, v, u} J R E O (a + 1)).val.app U
        ((E.d a (a + 1)).val.app U x))).app W).hom φ =
    (((homComplexπ (R := R) (homComplex (R := R) E O) O (a + 1) q k h).val.app U
      (((homComplex (R := R) (homComplex (R := R) E O) O).d a (a + 1)).val.app U
        ((betaTerm.{c, v, u} J R E O a).val.app U x))).app W).hom φ
  rw [betaTerm_apply.{c, v, u} J R]
  rw [differential_apply.{c, v, u} J R (homComplex (R := R) E O) O
    a q k (q + a) (q + 1) h rfl (by omega)]
  rw [betaTerm_apply.{c, v, u} J R, betaTerm_apply.{c, v, u} J R]
  rw [differential_apply.{c, v, u} J R E O q a k (q + a) (a + 1)
    (by omega) (add_comm a q) (by omega)]
  have hn := PresheafOfModules.naturality_apply
    (E.d a (a + 1)).val W.unop.hom.op x
  rw [← hn]
  simp only [Units.smul_def, map_zsmul, mul_add, add_mul, mul_one, one_mul,
    Int.negOnePow_add, mul_smul]
  rcases Int.units_eq_one_or a.negOnePow with ha | ha <;>
    rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
    rcases Int.units_eq_one_or (a * q).negOnePow with haq | haq <;>
    simp [ha, hq, haq] <;> abel

private noncomputable def betaChain (E O : CX.{c, v, u} J R) :
    E ⟶ homComplex (R := R) (homComplex (R := R) E O) O where
  f := betaTerm.{c, v, u} J R E O
  comm' a b h := by
    have hb : a + 1 = b := h
    subst b
    exact (betaTerm_comm.{c, v, u} J R E O a).symm

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma homPre_proj (E E' O : CX.{c, v, u} J R) (f : E' ⟶ E)
    (n a b : ℤ) (h : a + n = b) :
    (((homComplexFunctor (R := R)).map f.op).app O).f n ≫
      homComplexπ (R := R) E' O n a b h =
    homComplexπ (R := R) E O n a b h ≫
      SheafOfModules.homObjMap (R := R) (f.f a) (𝟙 (O.X b)) := by
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using
    (homComplexFunctor_map_f_π (R := R) f (𝟙 O) n a b h)

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma homPre_apply (E E' O : CX.{c, v, u} J R) (f : E' ⟶ E)
    (n a b : ℤ) (h : a + n = b) (U : Cᵒᵖ)
    (φ : ((homComplex (R := R) E O).X n).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (E'.X a).val.obj (op W.unop.left)) :
    (((homComplexπ (R := R) E' O n a b h).val.app U
      (((((homComplexFunctor (R := R)).map f.op).app O).f n).val.app U φ)).app W).hom x =
    (((homComplexπ (R := R) E O n a b h).val.app U φ).app W).hom
      ((f.f a).val.app (op W.unop.left) x) := by
  have he := congrArg (fun t ↦ (evalAt.{c, v, u} J R (E'.X a) (O.X b) U W x)
    (t.val.app U φ)) (homPre_proj.{c, v, u} J R E E' O f n a b h)
  with_unfolding_all exact he

-- The two nested product-Hom projections carry independent site universes.
omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma betaChain_natural (E E' O : CX.{c, v, u} J R) (f : E ⟶ E') :
    f ≫ betaChain.{c, v, u} J R E' O = betaChain.{c, v, u} J R E O ≫
      ((homComplexFunctor (R := R)).map
        (((homComplexFunctor (R := R)).map f.op).app O).op).app O := by
  apply HomologicalComplex.hom_ext
  intro a
  apply homComplex_hom_ext
  intro q k h
  apply homExt.{c, v, u} J R
  intro U x W φ
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change
    (((homComplexπ (R := R) (homComplex (R := R) E' O) O a q k h).val.app U
      ((betaTerm.{c, v, u} J R E' O a).val.app U ((f.f a).val.app U x))).app W).hom φ =
    (((homComplexπ (R := R) (homComplex (R := R) E' O) O a q k h).val.app U
      (((((homComplexFunctor (R := R)).map
        (((homComplexFunctor (R := R)).map f.op).app O).op).app O).f a).val.app U
          ((betaTerm.{c, v, u} J R E O a).val.app U x))).app W).hom φ
  rw [betaTerm_apply.{c, v, u} J R]
  erw [homPre_apply.{c, v, u} J R (homComplex (R := R) E O)
    (homComplex (R := R) E' O) O (((homComplexFunctor (R := R)).map f.op).app O)
    a q k h U ((betaTerm.{c, v, u} J R E O a).val.app U x) W φ]
  change _ = (((homComplexπ (R := R) (homComplex (R := R) E O) O a q k h).val.app U
    ((betaTerm.{c, v, u} J R E O a).val.app U x)).app W).hom _
  erw [betaTerm_apply.{c, v, u} J R, homPre_apply.{c, v, u} J R]
  have hn := PresheafOfModules.naturality_apply (f.f a).val W.unop.hom.op x
  have he := congrArg (fun y ↦ (a * q).negOnePow •
    (((homComplexπ (R := R) E' O q a k (by omega)).val.app (op W.unop.left) φ).app
      (op (Over.mk (𝟙 W.unop.left)))).hom y) hn
  with_unfolding_all exact he.symm

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma zeroSection (B : Mod.{c, v, u} J R) (hB : IsZero B)
    (U : Cᵒᵖ) (y : B.val.obj U) : y = 0 := by
  exact congrArg (fun f : B ⟶ B ↦ f.val.app U y) (hB.eq_of_tgt (𝟙 B) 0)

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma homZero {A B X : Mod.{c, v, u} J R} (hB : IsZero B)
    (f g : X ⟶ SheafOfModules.homObj (R := R) A B) : f = g := by
  apply homExt.{c, v, u} J R
  intro U x W y
  exact (zeroSection.{c, v, u} J R B hB _ _).trans
    (zeroSection.{c, v, u} J R B hB _ _).symm

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma beta_post_pre_apply (E O I P V : CX.{c, v, u} J R)
    (p : P ⟶ E) (t : V ⟶ homComplex (R := R) E O) (eta : O ⟶ I)
    (a b : ℤ) (U : Cᵒᵖ) (x : (P.X a).val.obj U) (y : (V.X b).val.obj U) :
    (((homComplexπ (R := R) V I a b (a + b) (add_comm b a)).val.app U
      ((((homComplexFunctor (R := R)).obj (op V)).map eta).f a |>.val.app U
        (((((homComplexFunctor (R := R)).map t.op).app O).f a).val.app U
          ((betaTerm.{c, v, u} J R E O a).val.app U ((p.f a).val.app U x))))).app
            (op (Over.mk (𝟙 U.unop)))).hom y =
    (a * b).negOnePow •
      (((homComplexπ (R := R) P I b a (a + b) rfl).val.app U
        ((((homComplexFunctor (R := R)).obj (op P)).map eta).f b |>.val.app U
          (((((homComplexFunctor (R := R)).map p.op).app O).f b).val.app U
            ((t.f b).val.app U y)))).app (op (Over.mk (𝟙 U.unop)))).hom x := by
  -- Pin the complexes and degrees before matching the nested Hom evaluations.
  erw [homPost_apply.{c, v, u} J R V O I eta a b (a + b) (add_comm b a) U,
    homPost_apply.{c, v, u} J R P O I eta b a (a + b) rfl U,
    homPre_apply.{c, v, u} J R (homComplex (R := R) E O) V O t
      a b (a + b) (add_comm b a) U,
    homPre_apply.{c, v, u} J R E P O p b a (a + b) rfl U,
    betaTerm_apply.{c, v, u} J R E O a b (a + b) (add_comm b a) U]
  simp only [Over.mk_left, Over.mk_hom, unop_op, op_unop, op_id,
    restriction_id.{c, v, u} J R, Units.smul_def]
  have he := map_zsmul ((eta.f (a + b)).val.app U).hom
    ((a * b).negOnePow : ℤ)
    ((((homComplexπ (R := R) E O b a (a + b) rfl).val.app U
      ((t.f b).val.app U y)).app (op (Over.mk (𝟙 U.unop)))).hom
        ((p.f a).val.app U x))
  with_unfolding_all exact he

section ClosedCalculation

variable {D : Type*} [Category* D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H)

private lemma uncurry_pre (X A B O : D) (f : X ⟶ H.obj (op A, O)) (p : B ⟶ A) :
    (S.transpose X B O).symm (f ≫ H.map (Prod.mkHom p.op (𝟙 O))) =
      S.tensor.map (Prod.mkHom (𝟙 X) p) ≫ (S.transpose X A O).symm f := by
  let := S.monoidal
  change ((S.adjunction B).homEquiv X O).symm
    (f ≫ H.map (Prod.mkHom p.op (𝟙 O))) =
      (𝟙 X ⊗ₘ p) ≫ ((S.adjunction A).homEquiv X O).symm f
  erw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  erw [Functor.map_comp, Category.assoc, S.evaluation_naturality]
  change (f ▷ B) ≫ (H.obj (op A, O) ◁ p) ≫ (S.adjunction A).counit.app O =
    (𝟙 X ⊗ₘ p) ≫ (f ▷ A) ≫ (S.adjunction A).counit.app O
  rw [← tensorHom_id, ← tensorHom_id, ← id_tensorHom]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp]

private lemma uncurry_swap
    (s : @SymmetricCategory D _ S.monoidal)
    (A B P T O : D) (p : P ⟶ A) (t : T ⟶ B) (c : B ⟶ H.obj (op A, O)) :
    (S.transpose P T O).symm
      (p ≫ S.transpose A (H.obj (op A, O)) O
        ((s.braiding A (H.obj (op A, O))).hom ≫ S.evaluation A O) ≫
        H.map (Prod.mkHom c.op (𝟙 O)) ≫
        H.map (Prod.mkHom t.op (𝟙 O))) =
    (s.braiding P T).hom ≫
      (S.transpose T P O).symm
        (t ≫ c ≫ H.map (Prod.mkHom p.op (𝟙 O))) := by
  let := S.monoidal
  let := s
  simp only [← Functor.map_comp, prod_comp, ← op_comp, Category.id_comp]
  simp only [← Category.assoc]
  erw [uncurry_pre S, uncurry_pre S]
  dsimp only [CoefficientClosedStructure.transpose]
  erw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  change (𝟙 P ⊗ₘ (t ≫ c)) ≫ (p ▷ H.obj (op A, O)) ≫
      (β_ A (H.obj (op A, O))).hom ≫ S.evaluation A O =
    (β_ P T).hom ≫ (𝟙 T ⊗ₘ p) ≫
      ((S.adjunction A).homEquiv T O).symm (t ≫ c)
  erw [Adjunction.homEquiv_counit]
  change _ = (β_ P T).hom ≫ (𝟙 T ⊗ₘ p) ≫ ((t ≫ c) ▷ A) ≫ _
  rw [← tensorHom_id, ← tensorHom_id]
  simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.comp_id, Category.id_comp]
  simpa only [Category.assoc, CoefficientClosedStructure.evaluation] using
    congrArg (fun f ↦ f ≫ S.evaluation A O)
    (BraidedCategory.braiding_naturality p (t ≫ c))

private lemma bidual_eq_of_uncurry
    (s : @SymmetricCategory D _ S.monoidal)
    (A B P T O : D) (p : P ⟶ A) (t : T ⟶ B) (c : B ⟶ H.obj (op A, O))
    (d : A ⟶ H.obj (op B, O)) [Epi p]
    [Mono (H.map (Prod.mkHom t.op (𝟙 O)))]
    (h : (S.transpose P T O).symm (p ≫ d ≫ H.map (Prod.mkHom t.op (𝟙 O))) =
      (s.braiding P T).hom ≫ (S.transpose T P O).symm
        (t ≫ c ≫ H.map (Prod.mkHom p.op (𝟙 O)))) :
    S.transpose A (H.obj (op A, O)) O
        ((s.braiding A (H.obj (op A, O))).hom ≫ S.evaluation A O) ≫
      H.map (Prod.mkHom c.op (𝟙 O)) = d := by
  apply (cancel_epi p).1
  apply (cancel_mono (H.map (Prod.mkHom t.op (𝟙 O)))).1
  apply (S.transpose P T O).symm.injective
  have hu := uncurry_swap S s A B P T O p t c
  simpa only [Category.assoc] using hu.trans h.symm

-- Transport the representative equality across the two comparison isomorphisms.
private lemma uncurry_model_swap {A B X Y Z : D}
    (i : X ≅ A) (j : Y ≅ B) (swap : X ⟶ Y) (s : A ⟶ B)
    (f : A ⟶ Z) (g : B ⟶ Z) (v : X ⟶ Z) (u : Y ⟶ Z)
    (hf : i.hom ≫ f = v) (hg : j.hom ≫ g = u)
    (hv : v = swap ≫ u) (hs : i.hom ≫ s = swap ≫ j.hom) :
    f = s ≫ g := by
  apply (cancel_epi i.hom).1
  calc
    i.hom ≫ f = v := hf
    _ = swap ≫ u := hv
    _ = swap ≫ (j.hom ≫ g) := congrArg (fun k ↦ swap ≫ k) hg.symm
    _ = i.hom ≫ (s ≫ g) := by rw [← Category.assoc, ← hs, Category.assoc]

end ClosedCalculation

private noncomputable def comparison (E F : CX.{c, v, u} J R) :
    DerivedCategory.Q.obj (homComplex (R := R) E F) ⟶
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj F) :=
  DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op E)).map
    ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app F)) ≫
      (coefficientHomResolutionIso.{u, c, v, w} J R E F).inv

private lemma resolutionIso_pre (E P F : CX.{c, v, u} J R) (p : P ⟶ E) :
    DerivedCategory.Q.map (((homComplexFunctor (R := R)).map p.op).app
      ((coefficientHomResolution.{u, c, v} J R).obj F)) ≫
        (coefficientHomResolutionIso.{u, c, v, w} J R P F).inv =
      (coefficientHomResolutionIso.{u, c, v, w} J R E F).inv ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          (Prod.mkHom (DerivedCategory.Q.map p).op (𝟙 (DerivedCategory.Q.obj F))) := by
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J R).1
  unfold coefficientHomResolutionIso
  let α := Localization.fac
    ((𝟭 (CX.{c, v, u} J R)ᵒᵖ).prod
      (CochainComplex.kInjectiveResolutionFunctor.{max c v u} (Mod.{c, v, u} J R)) ⋙
      Functor.uncurry.obj (homComplexFunctor.{c, v, max c v u, max c v u} (R := R)) ⋙
        (DerivedCategory.Q : CX.{c, v, u} J R ⥤ _))
    (derivedInternalHomOfUniverses_inverts.{c, v, u, w} J R _
      (CochainComplex.toKInjectiveResolution.{max c v u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} _ M⟩))
    ((DerivedCategory.Q : CX.{c, v, u} J R ⥤ _).op.prod DerivedCategory.Q)
  simpa [α, coefficientHomResolution, derivedInternalHomOfUniverses] using
    α.inv.naturality (Prod.mkHom p.op (𝟙 F))

private lemma comparison_pre (E P F : CX.{c, v, u} J R) (p : P ⟶ E) :
    DerivedCategory.Q.map (((homComplexFunctor (R := R)).map p.op).app F) ≫
      comparison.{c, v, u, w} J R P F =
    comparison.{c, v, u, w} J R E F ≫
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
        (Prod.mkHom (DerivedCategory.Q.map p).op (𝟙 (DerivedCategory.Q.obj F))) := by
  unfold comparison
  rw [← Category.assoc, ← Functor.map_comp,
    ← NatTrans.naturality, Functor.map_comp, Category.assoc, resolutionIso_pre]
  simp only [Category.assoc]

-- Naturality after an arbitrary map into the ordinary Hom complex.
private lemma comparison_pre_comp (E P F V : CX.{c, v, u} J R) (p : P ⟶ E)
    (t : V ⟶ homComplex (R := R) E F) :
    DerivedCategory.Q.map (t ≫ ((homComplexFunctor (R := R)).map p.op).app F ≫
      ((homComplexFunctor (R := R)).obj (op P)).map
        ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app F)) ≫
      (coefficientHomResolutionIso.{u, c, v, w} J R P F).inv =
    DerivedCategory.Q.map t ≫ comparison.{c, v, u, w} J R E F ≫
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
        (Prod.mkHom (DerivedCategory.Q.map p).op (𝟙 (DerivedCategory.Q.obj F))) := by
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun f ↦ DerivedCategory.Q.map t ≫ f)
    (comparison_pre.{c, v, u, w} J R E P F p)

omit [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)] in
private lemma total_ext (P V I : CX.{c, v, u} J R)
    (f g : (coefficientTotalTensor.{u, c, v} J R).obj (P, V) ⟶ I)
    (h : ∀ (a b : ℤ) (U : Cᵒᵖ) (x : (P.X a).val.obj U) (y : (V.X b).val.obj U),
      (f.f (a + b)).val.app U
          (coefficientTensorGenerator.{u, c, v} J R P V a b (a + b) rfl U x y) =
        (g.f (a + b)).val.app U
          (coefficientTensorGenerator.{u, c, v} J R P V a b (a + b) rfl U x y)) :
    f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  change a + b = k at hab
  subst k
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := R) (P.X a) (V.X b)).inv).1
  apply ((PresheafOfModules.sheafificationAdjunction.{max c v u}
    (𝟙 ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)).homEquiv
        ((P.X a).val ⊗ (V.X b).val) (I.X (a + b))).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h a b U

-- The signed chain-model identity gives symmetry of the derived uncurrying maps.
private lemma comparison_uncurry_swap
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (Mod.{c, v, u} J R)) _ S.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, u, w} J R S T s)
    (E O P V : CX.{c, v, u} J R)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hV : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) V)
    (p : P ⟶ E) (t : V ⟶ homComplex (R := R) E O) :
    let eta := (SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app O
    let I := (coefficientHomResolution.{u, c, v} J R).obj O
    let g : V ⟶ homComplex (R := R) P I :=
      t ≫ ((homComplexFunctor (R := R)).map p.op).app O ≫
        ((homComplexFunctor (R := R)).obj (op P)).map eta
    let h : P ⟶ homComplex (R := R) V I :=
      p ≫ betaChain.{c, v, u} J R E O ≫
        ((homComplexFunctor (R := R)).map t.op).app O ≫
        ((homComplexFunctor (R := R)).obj (op V)).map eta
    (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj V)
        (DerivedCategory.Q.obj O)).symm
      (DerivedCategory.Q.map h ≫ (coefficientHomResolutionIso.{u, c, v, w} J R V O).inv) =
      (s.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj V)).hom ≫
        (S.transpose (DerivedCategory.Q.obj V) (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj O)).symm
          (DerivedCategory.Q.map g ≫
            (coefficientHomResolutionIso.{u, c, v, w} J R P O).inv) := by
  intro eta I g h
  obtain ⟨ug, hug, hng⟩ := T.uncurry_model ⟨V, hV⟩ ⟨P, hP⟩ O g
  obtain ⟨vh, hvh, hnh⟩ := T.uncurry_model ⟨P, hP⟩ ⟨V, hV⟩ O h
  obtain ⟨swap, hswap, hswapQ⟩ := coh.symmetry_model P V hP hV
  have hvg : vh = swap.hom ≫ ug := by
    apply total_ext.{c, v, u} J R P V I
    intro a b U x y
    rw [hvh a b (a + b) rfl (add_comm b a) U x y]
    change coefficientHomSectionEvaluation.{u, c, v} J R P V O h
      a b (a + b) (add_comm b a) U x y =
        (ug.f (a + b)).val.app U
          ((swap.hom.f (a + b)).val.app U
            (coefficientTensorGenerator.{u, c, v} J R P V a b (a + b) rfl U x y))
    rw [hswap a b (a + b) rfl (add_comm b a) U x y]
    erw [Units.smul_def, map_zsmul, hug b a (a + b) (add_comm b a) rfl U y x]
    dsimp only [coefficientHomSectionEvaluation, coefficientHomComponent]
    exact beta_post_pre_apply.{c, v, u} J R E O I P V p t eta a b U x y
  exact uncurry_model_swap (T.iso J R S P V hP hV) (T.iso J R S V P hV hP)
    (DerivedCategory.Q.map swap.hom)
    (s.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj V)).hom
    _ _ _ _ hnh hng (by rw [hvg, Functor.map_comp, Category.assoc]) hswapQ

private lemma comparison_beta
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (Mod.{c, v, u} J R)) _ S.monoidal)
    (coh : RingedDerivedTensorCoherence.{c, v, u, w} J R S T s)
    (E O : CX.{c, v, u} J R) :
    S.transpose (DerivedCategory.Q.obj E)
        ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
          (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj O))
        (DerivedCategory.Q.obj O)
        ((s.braiding (DerivedCategory.Q.obj E)
          ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
            (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj O))).hom ≫
              S.evaluation (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj O)) ≫
      (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
        (Prod.mkHom (comparison.{c, v, u, w} J R E O).op
          (𝟙 (DerivedCategory.Q.obj O))) =
    DerivedCategory.Q.map (betaChain.{c, v, u} J R E O) ≫
      comparison.{c, v, u, w} J R (homComplex (R := R) E O) O := by
  let := S.monoidal
  let := s
  let D := homComplex (R := R) E O
  let eta := (SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app O
  let I := (coefficientHomResolution.{u, c, v} J R).obj O
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max c v u, c, v} E
  obtain ⟨V, t, hV, _, ht, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{max c v u, c, v} D
  let g : V ⟶ homComplex (R := R) P I :=
    t ≫ ((homComplexFunctor (R := R)).map p.op).app O ≫
      ((homComplexFunctor (R := R)).obj (op P)).map eta
  let h : P ⟶ homComplex (R := R) V I :=
    p ≫ betaChain.{c, v, u} J R E O ≫
      ((homComplexFunctor (R := R)).map t.op).app O ≫
      ((homComplexFunctor (R := R)).obj (op V)).map eta
  have hgQ : DerivedCategory.Q.map g ≫
      (coefficientHomResolutionIso.{u, c, v, w} J R P O).inv =
      DerivedCategory.Q.map t ≫ comparison.{c, v, u, w} J R E O ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          (Prod.mkHom (DerivedCategory.Q.map p).op (𝟙 (DerivedCategory.Q.obj O))) := by
    exact comparison_pre_comp.{c, v, u, w} J R E P O V p t
  have hhQ : DerivedCategory.Q.map h ≫
      (coefficientHomResolutionIso.{u, c, v, w} J R V O).inv =
      DerivedCategory.Q.map p ≫
        (DerivedCategory.Q.map (betaChain.{c, v, u} J R E O) ≫
          comparison.{c, v, u, w} J R D O) ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          (Prod.mkHom (DerivedCategory.Q.map t).op (𝟙 (DerivedCategory.Q.obj O))) := by
    simpa only [h, Functor.map_comp, Category.assoc] using
      comparison_pre_comp.{c, v, u, w} J R D V O P t
        (p ≫ betaChain.{c, v, u} J R E O)
  have hs : (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj V)
        (DerivedCategory.Q.obj O)).symm
      (DerivedCategory.Q.map h ≫ (coefficientHomResolutionIso.{u, c, v, w} J R V O).inv) =
      (s.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj V)).hom ≫
        (S.transpose (DerivedCategory.Q.obj V) (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj O)).symm
          (DerivedCategory.Q.map g ≫
            (coefficientHomResolutionIso.{u, c, v, w} J R P O).inv) := by
    exact comparison_uncurry_swap.{c, v, u, w} J R S T s coh E O P V hP hV p t
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
  have : IsIso (DerivedCategory.Q.map t) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 ht
  have : IsIso (Prod.mkHom (DerivedCategory.Q.map t).op
      (𝟙 (DerivedCategory.Q.obj O))) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map
      (Prod.mkHom (DerivedCategory.Q.map t).op (𝟙 (DerivedCategory.Q.obj O)))) :=
    inferInstance
  simp only [hhQ, hgQ] at hs
  exact bidual_eq_of_uncurry
    (D := DerivedCategory (Mod.{c, v, u} J R))
    (H := derivedInternalHomOfUniverses.{c, v, u, w} J R)
    S s (DerivedCategory.Q.obj E)
    (DerivedCategory.Q.obj D) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj V)
    (DerivedCategory.Q.obj O) (DerivedCategory.Q.map p) (DerivedCategory.Q.map t)
    (comparison.{c, v, u, w} J R E O)
    (DerivedCategory.Q.map (betaChain.{c, v, u} J R E O) ≫
      comparison.{c, v, u, w} J R D O) hs

/-- Signed ordinary biduality is natural and agrees with the derived evaluation transpose
under the two fixed augmentation comparisons, without a flatness hypothesis.

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X (section-hom-complexes),
0A92 (lemma-evaluate-and-more) and 0A97 (lemma-internal-hom-evaluate)
(blueprint: lem-sfb-ringed-signed-bidual-localization).

Proof plan, following the node's eight steps:
1. Use the actual Hom-product projections and localized sheaf Hom. For x in degree a,
   its q-component sends phi to (-1)^(a*q) phi(x) when a+q=0. Evaluation commutes
   with every restriction and is linear. All other coefficient-degree targets are zero.
   Product and sheaf-Hom extensionality give uniqueness, without summing components.
2. For q=-a-1 the Hom differential gives d_D(phi)=-(-1)^q phi d_E. Consequently
   d_B beta(x) has sign (-1)^(a+1+a*(q+1)+q+1)=(-1)^((a+1)*q), the sign of
   beta(d_E x). In other degrees both targets vanish. This proves the chain-map identity.
3. For f:E to E', both naturality composites evaluate to (-1)^(a*q) phi(f(x)).
   Check all localized sections and product projections to obtain the chain-map equality.
4. Put I=I(O). The hypotheses make Hom(E,eta_O) and Hom(D,eta_O) quasi-isomorphisms.
   Their localizations followed by the inverse fixed Hom factorization are gamma_E
   and gamma_D. Use the fixed K-injective comparison throughout (0A95, 08J7).
5. Choose K-flat flat-term resolutions p:P to E and t:T to D (06YS). The chain maps
   g=Hom(p,I) Hom(E,eta_O) t and h=Hom(t,I) Hom(D,eta_O) beta_E p localize to
   H(Qp,O) gamma_E Qt and H(Qt,O) gamma_D Q(beta_E) Qp respectively.
6. The stipulated uncurrying model on T,P identifies the uncurrying of Qg with
   epsilon_(QE,O) after (gamma_E Qt tensor Qp). On generators its chain model is
   u(tau tensor x)=eta_O(t(tau)(p(x))), followed by the inverse localized augmentation.
7. Apply the same model on P,T to h. Its chain model v(x tensor tau) is
   (-1)^(a*q) u(tau tensor x), and is zero off a+q=0. Thus v=u after the actual
   signed total-tensor swap. Sheafification and coproduct inclusions determine these
   maps, and the recorded symmetry normalization identifies their derived images.
8. Transposition naturality and symmetry naturality give exactly this same uncurrying
   for H(Qt,O) H(gamma_E,O) b_(QE) Qp. Injectivity of transposition identifies it
   with Qh; cancel Qp and H(Qt,O). Neither E nor D was assumed K-flat, bounded or perfect.
-/
theorem ringed_signed_bidual_localization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (s : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (_coherence : RingedDerivedTensorCoherence.{c, v, u, w} J R S T s) :
    ∃ β : ∀ E : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
        E ⟶ homComplex (R := R)
          (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
          (ringedTensorUnitComplex.{c, v, u} J R),
      ∀ E : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ,
        (∀ (a q : ℤ) (h : a + q = 0) (h' : q + a = 0) (U : Cᵒᵖ)
          (x : (E.X a).val.obj U) (W : (Over U.unop)ᵒᵖ)
          (φ : ((homComplex (R := R) E
            (ringedTensorUnitComplex.{c, v, u} J R)).X q).val.obj (op W.unop.left)),
          (((coefficientHomComponent.{u, c, v} J R
            (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
            (ringedTensorUnitComplex.{c, v, u} J R) a q 0 h').val.app U
              (((β E).f a).val.app U x)).app W).hom φ =
            (a * q).negOnePow •
              (((coefficientHomComponent.{u, c, v} J R E
                (ringedTensorUnitComplex.{c, v, u} J R) q a 0 h).val.app
                  (op W.unop.left) φ).app (op (Over.mk (𝟙 W.unop.left)))).hom
                    ((E.X a).val.map W.unop.hom.op x)) ∧
        (∀ β' : E ⟶ homComplex (R := R)
            (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
            (ringedTensorUnitComplex.{c, v, u} J R),
          (∀ (a q : ℤ) (h : a + q = 0) (h' : q + a = 0) (U : Cᵒᵖ)
            (x : (E.X a).val.obj U) (W : (Over U.unop)ᵒᵖ)
            (φ : ((homComplex (R := R) E
              (ringedTensorUnitComplex.{c, v, u} J R)).X q).val.obj (op W.unop.left)),
            (((coefficientHomComponent.{u, c, v} J R
              (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
              (ringedTensorUnitComplex.{c, v, u} J R) a q 0 h').val.app U
                ((β'.f a).val.app U x)).app W).hom φ =
              (a * q).negOnePow •
                (((coefficientHomComponent.{u, c, v} J R E
                  (ringedTensorUnitComplex.{c, v, u} J R) q a 0 h).val.app
                    (op W.unop.left) φ).app (op (Over.mk (𝟙 W.unop.left)))).hom
                      ((E.X a).val.map W.unop.hom.op x)) →
          β' = β E) ∧
        (∀ (a q k : ℤ) (h : q + a = k) (_hk : k ≠ 0),
          (β E).f a ≫ coefficientHomComponent.{u, c, v} J R
            (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
            (ringedTensorUnitComplex.{c, v, u} J R) a q k h = 0) ∧
        (∀ (E' : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ) (f : E ⟶ E'),
          f ≫ β E' = β E ≫
            ((homComplexFunctor (R := R)).map
              (((homComplexFunctor (R := R)).map f.op).app
                (ringedTensorUnitComplex.{c, v, u} J R)).op).app
                  (ringedTensorUnitComplex.{c, v, u} J R)) ∧
        (∀ (_hE : QuasiIso (((homComplexFunctor (R := R)).obj (op E)).map
              ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app
                (ringedTensorUnitComplex.{c, v, u} J R))))
          (_hD : QuasiIso (((homComplexFunctor (R := R)).obj
              (op (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)))).map
                ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app
                  (ringedTensorUnitComplex.{c, v, u} J R)))),
          ∃ γE : DerivedCategory.Q.obj
              (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)) ≅
            (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
              (op (DerivedCategory.Q.obj E),
                DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)),
          ∃ γD : DerivedCategory.Q.obj (homComplex (R := R)
              (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
              (ringedTensorUnitComplex.{c, v, u} J R)) ≅
            (derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
              (op (DerivedCategory.Q.obj
                (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))),
                DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)),
            γE.hom = DerivedCategory.Q.map
              (((homComplexFunctor (R := R)).obj (op E)).map
                ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app
                  (ringedTensorUnitComplex.{c, v, u} J R))) ≫
              (coefficientHomResolutionIso.{u, c, v, w} J R E
                (ringedTensorUnitComplex.{c, v, u} J R)).inv ∧
            γD.hom = DerivedCategory.Q.map
              (((homComplexFunctor (R := R)).obj
                (op (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R)))).map
                  ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app
                    (ringedTensorUnitComplex.{c, v, u} J R))) ≫
              (coefficientHomResolutionIso.{u, c, v, w} J R
                (homComplex (R := R) E (ringedTensorUnitComplex.{c, v, u} J R))
                (ringedTensorUnitComplex.{c, v, u} J R)).inv ∧
            S.transpose (DerivedCategory.Q.obj E)
                ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
                  (op (DerivedCategory.Q.obj E),
                    DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))
                (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))
                ((s.braiding (DerivedCategory.Q.obj E)
                  ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj
                    (op (DerivedCategory.Q.obj E),
                      DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))).hom ≫
                  S.evaluation (DerivedCategory.Q.obj E)
                    (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R))) ≫
              (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
                (Prod.mkHom γE.hom.op
                  (𝟙 (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))) =
            DerivedCategory.Q.map (β E) ≫ γD.hom) := by
  refine ⟨fun E ↦ betaChain.{c, v, u} J R E (ringedTensorUnitComplex.{c, v, u} J R), ?_⟩
  intro E
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a q h h' U x W φ
    exact betaTerm_apply.{c, v, u} J R E _ a q 0 h' U x W φ
  · intro b hb
    apply HomologicalComplex.hom_ext
    intro a
    apply homComplex_hom_ext
    intro q k h
    by_cases hk : k = 0
    · cases hk
      apply homExt.{c, v, u} J R
      intro U x W φ
      exact (hb a q (by omega) h U x W φ).trans
        (betaTerm_apply.{c, v, u} J R E _ a q 0 h U x W φ).symm
    · apply homZero.{c, v, u} J R
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hk
  · intro a q k h hk
    apply homZero.{c, v, u} J R
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hk
  · intro E' f
    exact betaChain_natural.{c, v, u} J R E E' _ f
  · intro hE hD
    let O := ringedTensorUnitComplex.{c, v, u} J R
    let D := homComplex (R := R) E O
    have hE' : IsIso (DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op E)).map
        ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app O))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hE
    have hD' : IsIso (DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op D)).map
        ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app O))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hD
    refine ⟨asIso (DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op E)).map
        ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app O))) ≪≫
      (coefficientHomResolutionIso.{u, c, v, w} J R E O).symm,
      asIso (DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op D)).map
        ((SfbHomFilteredColimit.resolutionUnit.{c, v, u} J R).app O))) ≪≫
      (coefficientHomResolutionIso.{u, c, v, w} J R D O).symm, rfl, rfl, ?_⟩
    exact comparison_beta.{c, v, u, w} J R S T s _coherence E O

end CategoryTheory
