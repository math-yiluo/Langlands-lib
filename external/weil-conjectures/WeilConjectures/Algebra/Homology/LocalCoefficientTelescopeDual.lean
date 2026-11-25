/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # The dual of the free coefficient telescope

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af.
-/

@[expose] public section

universe u w wSlice

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- The countable coproduct of the coefficient unit on the slice site.
Source: Stacks Project, Tag 0997 (auxiliary; not a blueprint node). -/
noncomputable abbrev localCoefficientFree {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C) :=
  ∐ fun _ : ℕ ↦ SheafOfModules.unit ((localCoefficientRings R).over U)

/-- Identity minus the forward multiplication shift on the free sum.
Source: Stacks Project, Tag 0997 (auxiliary; not a blueprint node). -/
noncomputable def localCoefficientTelescopeMap {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) : localCoefficientFree R U ⟶ localCoefficientFree R U :=
  Sigma.desc (fun n : ℕ ↦
    Sigma.ι (fun _ : ℕ ↦ SheafOfModules.unit ((localCoefficientRings R).over U)) n -
      localSectionMultiplication R U f _ ≫
        Sigma.ι (fun _ : ℕ ↦ SheafOfModules.unit ((localCoefficientRings R).over U)) (n + 1))

private theorem singleZero_natural
    {B : Type*} [Category B] [HasZeroMorphisms B] [HasZeroObject B]
    {P P' : B} (f : P' ⟶ P) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P').inv ≫
        ((HomologicalComplex.single B (.up ℤ) 0).map f).f 0 =
      f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv := by
  rw [HomologicalComplex.single_map_f_self]
  simp only [Iso.inv_hom_id_assoc]

private theorem singleZero_map
    {B D : Type*} [Category B] [HasZeroMorphisms B] [HasZeroObject B] [Category D]
    (F : Bᵒᵖ ⥤ D) {P P' : B} (f : P' ⟶ P) :
    F.map (((HomologicalComplex.single B (.up ℤ) 0).map f).f 0).op ≫
        F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P').inv.op =
      F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv.op ≫ F.map f.op := by
  rw [← F.map_comp, ← op_comp, singleZero_natural, op_comp, F.map_comp]

private noncomputable def soleFactorIso {B : Type*} [Category B] [HasZeroMorphisms B]
    {f : ℤ → B} (c : Fan f) (hc : IsLimit c) (i : ℤ)
    (hz : ∀ j, j ≠ i → IsZero (f j)) : c.pt ≅ f i where
  hom := c.proj i
  inv := hc.lift (Fan.mk (f i) (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0))
  hom_inv_id := by
    apply hc.hom_ext
    rintro ⟨j⟩
    rw [Category.assoc, hc.fac]
    by_cases h : j = i
    · subst j
      simp
      rfl
    · exact (hz j h).eq_of_tgt _ _
  inv_hom_id := by
    change hc.lift (Fan.mk (f i)
      (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0)) ≫
      c.π.app (Discrete.mk i) = 𝟙 (f i)
    rw [hc.fac]
    simp

section AbstractHom

variable {B : Type*} [Category B] [Abelian B]

private noncomputable def abstractSingleZeroIso (P : B) :
    ((CochainComplex.singleFunctor B 0).obj P).X 0 ≅ P :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0 P

private noncomputable abbrev abstractHomMap
    (G : Bᵒᵖ ⥤ B ⥤ B) {P P' N N' : B} (f : P' ⟶ P) (g : N ⟶ N') :
    (G.obj (op P)).obj N ⟶ (G.obj (op P')).obj N' :=
  (G.map f.op).app N ≫ (G.obj (op P')).map g

private noncomputable def abstractProjection
    (G : Bᵒᵖ ⥤ B ⥤ B)
    (F : (CochainComplex B ℤ)ᵒᵖ ⥤
  CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (π : ∀ (L I : CochainComplex B ℤ) (n p q : ℤ), p + n = q →
    (((F.obj (op L)).obj I).X n ⟶ ((G.obj (op (L.X p))).obj (I.X q))))
    (P : B) (I : CochainComplex B ℤ) (n : ℤ) :
    ((F.obj (op ((CochainComplex.singleFunctor B 0).obj P))).obj I).X n ⟶
      ((G.obj (op P)).obj (I.X n)) :=
  π ((CochainComplex.singleFunctor B 0).obj P) I n 0 n (zero_add n) ≫
    abstractHomMap G (abstractSingleZeroIso P).inv (𝟙 (I.X n))

private theorem abstractProjection_isIso
    (G : Bᵒᵖ ⥤ B ⥤ B)
    [∀ N, (G.flip.obj N).Additive]
    (F : (CochainComplex B ℤ)ᵒᵖ ⥤
  CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (π : ∀ (L I : CochainComplex B ℤ) (n p q : ℤ), p + n = q →
    (((F.obj (op L)).obj I).X n ⟶ ((G.obj (op (L.X p))).obj (I.X q))))
    (hlim : ∀ (L I : CochainComplex B ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj I).X n)
        (fun p : ℤ ↦ π L I n p (p + n) rfl))))
    (P : B) (I : CochainComplex B ℤ) (n : ℤ) :
    IsIso (abstractProjection G F π P I n) := by
  classical
  let Pc := (CochainComplex.singleFunctor B 0).obj P
  have hz (p : ℤ) (hp : p ≠ 0) :
      IsZero (((G.obj (op (Pc.X p))).obj (I.X (p + n)))) := by
    exact (G.flip.obj (I.X (p + n))).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 P p hp).op
  have he := (soleFactorIso _ (hlim Pc I n).some 0 hz).isIso_hom
  change IsIso (π Pc I n 0 (0 + n) rfl) at he
  have helper {q : ℤ} (hq : 0 + n = q) : IsIso (π Pc I n 0 q hq) := by
    subst q
    exact he
  have hpi : IsIso (π Pc I n 0 n (zero_add n)) := helper (zero_add n)
  have ht : IsIso (abstractHomMap G
      (abstractSingleZeroIso P).inv (𝟙 (I.X n))) := by
    dsimp only [abstractHomMap]
    simp only [Functor.map_id, Category.comp_id]
    infer_instance
  exact IsIso.comp_isIso' hpi ht

private theorem abstractUnitProjection_precomp
    (G : Bᵒᵖ ⥤ B ⥤ B)
    (E : B) (ν : ∀ N, (G.obj (op E)).obj N ≅ N)
    (F : (CochainComplex B ℤ)ᵒᵖ ⥤
  CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (π : ∀ (L I : CochainComplex B ℤ) (n p q : ℤ), p + n = q →
    (((F.obj (op L)).obj I).X n ⟶ ((G.obj (op (L.X p))).obj (I.X q))))
    (hmap : ∀ (L L' I I' : CochainComplex B ℤ)
      (f : L' ⟶ L) (g : I ⟶ I') (n p q : ℤ) (h : p + n = q),
      (((F.map f.op).app I) ≫ (F.obj (op L')).map g).f n ≫ π L' I' n p q h =
        π L I n p q h ≫ abstractHomMap G (f.f p) (g.f q))
    (ev : ∀ I : CochainComplex B ℤ,
      (F.obj (op ((CochainComplex.singleFunctor B 0).obj (E)))).obj I ≅ I)
    (hev : ∀ (I : CochainComplex B ℤ) (n : ℤ),
      (ev I).hom.f n = abstractProjection G F π (E) I n ≫
        (ν (I.X n)).hom)
    {P : B} (f : E ⟶ P)
    (I : CochainComplex B ℤ) (n : ℤ) :
    ((F.map ((CochainComplex.singleFunctor B 0).map f).op).app I).f n ≫ (ev I).hom.f n =
      abstractProjection G F π P I n ≫
        abstractHomMap G f (𝟙 (I.X n)) ≫
          (ν (I.X n)).hom := by
  have h := hmap ((CochainComplex.singleFunctor B 0).obj P)
    ((CochainComplex.singleFunctor B 0).obj E) I I
    ((CochainComplex.singleFunctor B 0).map f) (𝟙 I) n 0 n (zero_add n)
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at h
  let t := abstractHomMap G (abstractSingleZeroIso P).inv (𝟙 (I.X n))
  let t' := abstractHomMap G
    (abstractSingleZeroIso E).inv (𝟙 (I.X n))
  let q := abstractHomMap G (((CochainComplex.singleFunctor B 0).map f).f 0) (𝟙 (I.X n))
  let g := abstractHomMap G f (𝟙 (I.X n))
  have swap : q ≫ t' = t ≫ g := by
    dsimp only [q, t', t, g, abstractHomMap]
    simp only [Functor.map_id, Category.comp_id]
    exact singleZero_map (G.flip.obj (I.X n)) f
  rw [hev]
  change _ ≫ ((π _ I n 0 n (zero_add n) ≫ t') ≫ (ν (I.X n)).hom) =
    (π _ I n 0 n (zero_add n) ≫ t) ≫ g ≫ (ν (I.X n)).hom
  calc
    _ = (((F.map ((CochainComplex.singleFunctor B 0).map f).op).app I).f n ≫
        π _ I n 0 n (zero_add n)) ≫ t' ≫ (ν (I.X n)).hom := by
          simp only [Category.assoc]
    _ = (π _ I n 0 n (zero_add n) ≫ q) ≫ t' ≫ (ν (I.X n)).hom := by rw [h]
    _ = (π _ I n 0 n (zero_add n) ≫ t) ≫ g ≫ (ν (I.X n)).hom := by
      rw [Category.assoc, ← Category.assoc q t', swap]
      simp only [Category.assoc]

private noncomputable def abstractFreeHomFan_isLimit
    (G : Bᵒᵖ ⥤ B ⥤ B)
    (E : B) (ν : ∀ N, (G.obj (op E)).obj N ≅ N)
    [∀ N, (G.flip.obj N).Additive] [HasCoproduct (fun _ : ℕ ↦ E)]
    (F : (CochainComplex B ℤ)ᵒᵖ ⥤
  CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (π : ∀ (L I : CochainComplex B ℤ) (n p q : ℤ), p + n = q →
    (((F.obj (op L)).obj I).X n ⟶ ((G.obj (op (L.X p))).obj (I.X q))))
    (hlim : ∀ (L I : CochainComplex B ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj I).X n)
        (fun p : ℤ ↦ π L I n p (p + n) rfl))))
    (hmap : ∀ (L L' I I' : CochainComplex B ℤ)
      (f : L' ⟶ L) (g : I ⟶ I') (n p q : ℤ) (h : p + n = q),
      (((F.map f.op).app I) ≫ (F.obj (op L')).map g).f n ≫ π L' I' n p q h =
        π L I n p q h ≫ abstractHomMap G (f.f p) (g.f q))
    (ev : ∀ I : CochainComplex B ℤ,
      (F.obj (op ((CochainComplex.singleFunctor B 0).obj (E)))).obj I ≅ I)
    (hev : ∀ (I : CochainComplex B ℤ) (n : ℤ),
      (ev I).hom.f n = abstractProjection G F π (E) I n ≫
        (ν (I.X n)).hom)
    (I : CochainComplex B ℤ)
    (ho : ∀ k : ℤ, IsLimit (Fan.mk ((G.obj (op (∐ fun _ : ℕ ↦ E))).obj (I.X k))
      (fun n : ℕ ↦ abstractHomMap G (Sigma.ι (fun _ : ℕ ↦ E) n) (𝟙 (I.X k))))) :
    IsLimit (Fan.mk ((F.obj
      (op ((CochainComplex.singleFunctor B 0).obj (∐ fun _ : ℕ ↦ E)))).obj I)
      (fun n : ℕ ↦ (F.map ((CochainComplex.singleFunctor B 0).map
        (Sigma.ι (fun _ : ℕ ↦ E) n)).op).app I ≫ (ev I).hom)) := by
  classical
  apply HomologicalComplex.isLimitOfEval
  intro k
  refine (isLimitMapConeFanMkEquiv (HomologicalComplex.eval _ _ k)
    (fun _ : ℕ ↦ I) _).symm ?_
  letI hprojection : IsIso (abstractProjection G F π ((∐ fun _ : ℕ ↦ E)) I k) :=
    abstractProjection_isIso G F π hlim _ I k
  refine Fan.IsLimit.ofIsos (ho k)
    (fun _ ↦ (ν (I.X k)).symm)
    (@asIso _ _ _ _ (abstractProjection G F π ((∐ fun _ : ℕ ↦ E)) I k) hprojection) ?_
  intro n
  change abstractProjection G F π ((∐ fun _ : ℕ ↦ E)) I k ≫
      abstractHomMap G (Sigma.ι (fun _ : ℕ ↦ E) n) (𝟙 (I.X k)) =
    (((F.map ((CochainComplex.singleFunctor B 0).map (Sigma.ι (fun _ : ℕ ↦ E) n)).op).app I).f k ≫
      (ev I).hom.f k) ≫ (ν (I.X k)).inv
  rw [abstractUnitProjection_precomp G E ν F π hmap ev hev]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem abstractEvaluation_scalar
    (G : Bᵒᵖ ⥤ B ⥤ B)
    (E : B) (ν : ∀ N, (G.obj (op E)).obj N ≅ N)
    (F : (CochainComplex B ℤ)ᵒᵖ ⥤
  CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (π : ∀ (L I : CochainComplex B ℤ) (n p q : ℤ), p + n = q →
    (((F.obj (op L)).obj I).X n ⟶ ((G.obj (op (L.X p))).obj (I.X q))))
    (hmap : ∀ (L L' I I' : CochainComplex B ℤ)
      (f : L' ⟶ L) (g : I ⟶ I') (n p q : ℤ) (h : p + n = q),
      (((F.map f.op).app I) ≫ (F.obj (op L')).map g).f n ≫ π L' I' n p q h =
        π L I n p q h ≫ abstractHomMap G (f.f p) (g.f q))
    (ev : ∀ I : CochainComplex B ℤ,
      (F.obj (op ((CochainComplex.singleFunctor B 0).obj (E)))).obj I ≅ I)
    (hev : ∀ (I : CochainComplex B ℤ) (n : ℤ),
      (ev I).hom.f n = abstractProjection G F π (E) I n ≫
        (ν (I.X n)).hom)
    (I : CochainComplex B ℤ) (b : E ⟶ E) (t : I ⟶ I)
    (hscalar : ∀ n, abstractHomMap G b (𝟙 (I.X n)) ≫ (ν (I.X n)).hom =
      (ν (I.X n)).hom ≫ t.f n) :
    (F.map ((CochainComplex.singleFunctor B 0).map b).op).app I ≫ (ev I).hom =
      (ev I).hom ≫ t := by
  ext n : 1
  change _ ≫ (ev I).hom.f n = (ev I).hom.f n ≫ t.f n
  rw [abstractUnitProjection_precomp G E ν F π hmap ev hev,
    hscalar, ← Category.assoc, ← hev]

end AbstractHom

private noncomputable def mapComplexProductFan_isLimit
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasProductsOfShape ℕ A]
    (I : CochainComplex A ℤ) [I.IsKInjective]
    (c : Fan (fun _ : ℕ ↦ I)) (hc : IsLimit c) :
    IsLimit (Fan.mk (DerivedCategory.Q.obj c.pt)
      (fun n : ℕ ↦ DerivedCategory.Q.map (c.proj n))) := by
  let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor (fun _ : ℕ ↦ I))
  have hP : IsLimit P := HomologicalComplex.isLimitConeOfHasLimitEval _
  have hD := (CochainComplex.termwise_product_isKInjective_and_isLimit
    (fun _ : ℕ ↦ I)).2.some
  have hD' := (Fan.isLimitMapConeEquiv DerivedCategory.Q _ P) hD
  let e := hc.conePointUniqueUpToIso hP
  refine Fan.IsLimit.ofIsos hD' (fun _ ↦ Iso.refl _) (DerivedCategory.Q.mapIso e) ?_
  intro n
  change DerivedCategory.Q.map e.hom ≫ DerivedCategory.Q.map (P.π.app ⟨n⟩) =
    DerivedCategory.Q.map (c.proj n) ≫ 𝟙 _
  rw [← Functor.map_comp, Category.comp_id]
  congr 1
  exact IsLimit.conePointUniqueUpToIso_hom_comp hc hP ⟨n⟩

section HomComplex

attribute [local irreducible] homComplexFunctor
  HomologicalComplex.single HomologicalComplex.singleObjXSelf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

private noncomputable abbrev modules :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

private noncomputable abbrev single := CochainComplex.singleFunctor (modules R) 0

private noncomputable abbrev unitModule : modules R :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

private noncomputable abbrev freeUnit : modules R := ∐ fun _ : ℕ ↦ unitModule R

set_option backward.isDefEq.respectTransparency false in
private theorem abstractHomMap_sheaf {P P' N N' : modules R}
    (f : P' ⟶ P) (g : N ⟶ N') :
    abstractHomMap (SheafOfModules.homFunctor R) f g =
      SheafOfModules.homObjMap (R := R) f g := by
  dsimp only [abstractHomMap, SheafOfModules.homFunctor]
  change SheafOfModules.homObjMap (R := R) f (𝟙 N) ≫
    SheafOfModules.homObjMap (R := R) (𝟙 P') g = _
  simpa only [Category.id_comp, Category.comp_id] using
    (SheafOfModules.homObjMap_comp_homObjMap (R := R) f (𝟙 P') (𝟙 N) g)

private noncomputable abbrev chosenProjections :=
  Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := R))

private noncomputable abbrev homProjection :=
  abstractProjection (SheafOfModules.homFunctor R)
    (homComplexFunctor.{u, u, u, u} (R := R)) (chosenProjections R)

private noncomputable def unitEvaluationIso (I : CochainComplex (modules R) ℤ) :
    ((homComplexFunctor.{u, u, u, u} (R := R)).obj
      (op ((single R).obj (unitModule R)))).obj I ≅ I := by
  have (n : ℤ) := homComplex_unit_evaluation_isIso J R I n
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso (homComplexUnitEvaluation J R I n))
    (fun n m h ↦ homComplex_unit_evaluation_comm J R I n m h)

set_option backward.isDefEq.respectTransparency false in
private theorem unitEvaluation_f (I : CochainComplex (modules R) ℤ) (k : ℤ) :
    (unitEvaluationIso R I).hom.f k = homProjection R (unitModule R) I k ≫
      (SheafOfModules.homObjUnitIso (R := R) (I.X k)).hom := by
  dsimp only [homProjection, abstractProjection]
  rw [abstractHomMap_sheaf]
  change (_ ≫ _ ≫ _) = ((_ ≫ _) ≫ _)
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency true in
private theorem rhomFreeFan_isLimit [HasDerivedCategory.{w} (modules R)]
    (I₀ : CochainComplex (modules R) ℤ ⥤ CochainComplex (modules R) ℤ)
    (η : 𝟭 (CochainComplex (modules R) ℤ) ⟶ I₀)
    (hI : ∀ M, QuasiIso (η.app M) ∧ (I₀.obj M).IsKInjective)
    (M : CochainComplex (modules R) ℤ) (L : DerivedCategory (modules R))
    (eL : DerivedCategory.Q.obj M ≅ L) (eI : DerivedCategory.Q.obj (I₀.obj M) ≅ L)
    (b : unitModule R ⟶ unitModule R) (t : I₀.obj M ⟶ I₀.obj M) (β : L ⟶ L)
    (ev : ∀ I : CochainComplex (modules R) ℤ,
      ((homComplexFunctor.{u, u, u, u} (R := R)).obj
        (op ((single R).obj (unitModule R)))).obj I ≅ I)
    (hFan : IsLimit (Fan.mk (((homComplexFunctor.{u, u, u, u} (R := R)).obj
        (op ((single R).obj (freeUnit R)))).obj (I₀.obj M))
      (fun n : ℕ ↦ ((homComplexFunctor.{u, u, u, u} (R := R)).map
        ((single R).map (Sigma.ι (fun _ : ℕ ↦ unitModule R) n)).op).app (I₀.obj M) ≫
          (ev (I₀.obj M)).hom)))
    (heval : ((homComplexFunctor.{u, u, u, u} (R := R)).map ((single R).map b).op).app (I₀.obj M) ≫
        (ev (I₀.obj M)).hom =
      (ev (I₀.obj M)).hom ≫ t)
    (hβ : DerivedCategory.Q.map t ≫ eI.hom = eI.hom ≫ β) :
    let S := DerivedCategory.singleFunctor (modules R) 0
    let H := (Functor.curry.obj (derivedInternalHom J R)).flip.obj L
    ∃ z : H.obj (op (S.obj (unitModule R))) ≅ L,
      Nonempty (IsLimit (Fan.mk (H.obj (op (S.obj (freeUnit R))))
        (fun n : ℕ ↦ H.map (S.map (Sigma.ι (fun _ : ℕ ↦ unitModule R) n)).op ≫ z.hom))) ∧
      H.map (S.map b).op ≫ z.hom = z.hom ≫ β := by
  classical
  let A := modules R
  let I := I₀.obj M
  have : I.IsKInjective := (hI M).2
  obtain ⟨c⟩ := derivedInternalHom_comparison J R I₀ η hI
  let S := DerivedCategory.singleFunctor A 0
  let H := (Functor.curry.obj (derivedInternalHom J R)).flip.obj L
  let H₀ := (Functor.curry.obj (derivedInternalHom J R)).flip.obj (DerivedCategory.Q.obj M)
  let G := (homComplexFunctor.{u, u, u, u} (R := R)).flip.obj I ⋙ DerivedCategory.Q
  let a₀ : S.op ⋙ H ≅ S.op ⋙ H₀ := Functor.isoWhiskerLeft S.op
    (((Functor.curry.obj (derivedInternalHom J R)).flip.mapIso eL.symm))
  let a₁ : S.op ⋙ H₀ ≅ (single R).op ⋙ G := NatIso.ofComponents
    (fun P ↦ c.app (op ((single R).obj P.unop), M)) (by
      intro P P' b
      have h := c.hom.naturality
        (show (op ((single R).obj P.unop), M) ⟶
            (op ((single R).obj P'.unop), M) from
          (((single R).map b.unop).op, 𝟙 M))
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.op_map,
        Functor.op_obj, Functor.id_map, Functor.id_obj, Functor.uncurry_obj_map] at h
      simp only [Functor.map_id, Category.comp_id] at h
      exact h)
  let a := a₀ ≪≫ a₁
  let v : ((homComplexFunctor.{u, u, u, u} (R := R)).obj
      (op ((single R).obj (unitModule R)))).obj I ⟶ I := (ev I).hom
  have hv : ((homComplexFunctor.{u, u, u, u} (R := R)).map ((single R).map b).op).app I ≫ v =
      v ≫ t := heval
  let z := a.app (op (unitModule R)) ≪≫ DerivedCategory.Q.mapIso (ev I) ≪≫ eI
  have hdFan := mapComplexProductFan_isLimit I _ hFan
  refine ⟨z, ⟨Fan.IsLimit.ofIsos hdFan
    (fun _ ↦ eI.symm) (a.app (op (freeUnit R))) ?_⟩, ?_⟩
  swap
  · have h := a.hom.naturality b.op
    change H.map (S.map b).op ≫ (a.app (op (unitModule R))).hom =
      (a.app (op (unitModule R))).hom ≫ DerivedCategory.Q.map
        (((homComplexFunctor.{u, u, u, u} (R := R)).map ((single R).map b).op).app I) at h
    change H.map (S.map b).op ≫
      ((a.app (op (unitModule R))).hom ≫ DerivedCategory.Q.map v ≫ eI.hom) =
      ((a.app (op (unitModule R))).hom ≫ DerivedCategory.Q.map v ≫ eI.hom) ≫ β
    rw [← Category.assoc, h, Category.assoc]
    rw [← Category.assoc (DerivedCategory.Q.map _) (DerivedCategory.Q.map v) eI.hom,
      ← Functor.map_comp, hv, Functor.map_comp]
    simp only [Category.assoc, hβ]
  intro n
  have h := a.hom.naturality (Sigma.ι (fun _ : ℕ ↦ unitModule R) n).op
  change H.map (S.map (Sigma.ι (fun _ : ℕ ↦ unitModule R) n)).op ≫
      (a.app (op (unitModule R))).hom =
    (a.app (op (freeUnit R))).hom ≫ DerivedCategory.Q.map
      (((homComplexFunctor.{u, u, u, u} (R := R)).map
        ((single R).map (Sigma.ι (fun _ : ℕ ↦ unitModule R) n)).op).app I) at h
  change (a.app (op (freeUnit R))).hom ≫ DerivedCategory.Q.map
      (((homComplexFunctor.{u, u, u, u} (R := R)).map
        ((single R).map (Sigma.ι (fun _ : ℕ ↦ unitModule R) n)).op).app I ≫ v) =
    (H.map (S.map (Sigma.ι (fun _ : ℕ ↦ unitModule R) n)).op ≫
      (a.app (op (unitModule R))).hom ≫ DerivedCategory.Q.map v ≫ eI.hom) ≫ eI.inv
  rw [Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← h, Category.assoc]

end HomComplex

private theorem dualTelescope
    {A B D : Type*} [Category A] [Preadditive A] [Category B] [Preadditive B]
    [Category D] [Preadditive D] (S : A ⥤ B) [S.Additive]
    (H : Bᵒᵖ ⥤ D) [H.Additive] (P : A) [HasCoproduct (fun _ : ℕ ↦ P)]
    (b : P ⟶ P) (d : (∐ fun _ : ℕ ↦ P) ⟶ ∐ fun _ : ℕ ↦ P)
    (hd : ∀ n, Sigma.ι (fun _ : ℕ ↦ P) n ≫ d =
      Sigma.ι (fun _ : ℕ ↦ P) n - b ≫ Sigma.ι (fun _ : ℕ ↦ P) (n + 1))
    (L : D) [HasProduct (fun _ : ℕ ↦ L)] (β : L ⟶ L)
    (z : H.obj (op (S.obj P)) ≅ L)
    (hc : IsLimit (Fan.mk (H.obj (op (S.obj (∐ fun _ : ℕ ↦ P))))
      (fun n : ℕ ↦ H.map (S.map (Sigma.ι (fun _ : ℕ ↦ P) n)).op ≫ z.hom)))
    (hβ : H.map (S.map b).op ≫ z.hom = z.hom ≫ β) :
    ∃ e : H.obj (op (S.obj (∐ fun _ : ℕ ↦ P))) ≅ ∏ᶜ (fun _ : ℕ ↦ L),
      H.map (S.map d).op ≫ e.hom =
        e.hom ≫ towerTransitionEndomorphism (K := fun _ : ℕ ↦ L) (fun _ ↦ β) := by
  let e := hc.conePointUniqueUpToIso (productIsProduct (fun _ : ℕ ↦ L))
  have he (n : ℕ) : e.hom ≫ Pi.π (fun _ : ℕ ↦ L) n =
      H.map (S.map (Sigma.ι (fun _ : ℕ ↦ P) n)).op ≫ z.hom :=
    IsLimit.conePointUniqueUpToIso_hom_comp hc (productIsProduct (fun _ : ℕ ↦ L)) ⟨n⟩
  refine ⟨e, ?_⟩
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, he]
  have hmap : H.map (S.map d).op ≫ H.map (S.map (Sigma.ι (fun _ : ℕ ↦ P) n)).op =
      H.map (S.map (Sigma.ι (fun _ : ℕ ↦ P) n)).op -
        H.map (S.map (Sigma.ι (fun _ : ℕ ↦ P) (n + 1))).op ≫ H.map (S.map b).op := by
    rw [← H.map_comp, ← op_comp, ← S.map_comp, hd,
      S.map_sub, op_sub, H.map_sub, S.map_comp, op_comp, H.map_comp]
  rw [← Category.assoc, hmap, Preadditive.sub_comp, Category.assoc, hβ]
  simp only [towerTransitionEndomorphism, towerProductShift,
    Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π, Preadditive.comp_sub,
    Category.assoc, he]
  rw [← Category.assoc e.hom (Pi.π (fun _ : ℕ ↦ L) (n + 1)) β, he, Category.assoc]

private noncomputable def sectionComplexMultiplication
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    (I : CochainComplex (ringedSiteModules.{u} ((localCoefficientRings R).over U)) ℤ) :
    I ⟶ I where
  f n := localSectionMultiplication R U f (I.X n)
  comm' n m _ := (localSectionMultiplication_naturality R U f (I.d n m)).symm

private theorem sectionComplexMultiplication_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    {I I' : CochainComplex (ringedSiteModules.{u} ((localCoefficientRings R).over U)) ℤ}
    (g : I ⟶ I') :
    g ≫ sectionComplexMultiplication R U f I' =
      sectionComplexMultiplication R U f I ≫ g := by
  ext n : 1
  exact localSectionMultiplication_naturality R U f (g.f n)

private noncomputable def restrictionRepresentative
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u} (localCoefficientRings R))) :
    Σ M : CochainComplex (ringedSiteModules.{u} ((localCoefficientRings R).over U)) ℤ,
      DerivedCategory.Q.obj M ≅ (localCoefficientDerivedRestriction R U).obj K :=
  haveI := (localCoefficientRestriction_exact R U).1
  haveI := (localCoefficientRestriction_exact R U).2.1
  haveI := (localCoefficientRestriction_exact R U).2.2
  let T := SheafOfModules.overFunctor.{u} (localCoefficientRings R) U
  let M₀ := DerivedCategory.Q.objPreimage K
  ⟨(T.mapHomologicalComplex (.up ℤ)).obj M₀,
    (T.mapDerivedCategoryFactors.app M₀).symm ≪≫
      (localCoefficientDerivedRestriction R U).mapIso (DerivedCategory.Q.objObjPreimageIso K)⟩

set_option backward.isDefEq.respectTransparency true in
private theorem restrictionRepresentative_scalar
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u} (localCoefficientRings R))) :
    DerivedCategory.Q.map
        (sectionComplexMultiplication R U f (restrictionRepresentative R U K).1) ≫
        (restrictionRepresentative R U K).2.hom =
      (restrictionRepresentative R U K).2.hom ≫
        (localSectionDerivedMultiplication R U f).app K := by
  let := (localCoefficientRestriction_exact R U).1
  let := (localCoefficientRestriction_exact R U).2.1
  let := (localCoefficientRestriction_exact R U).2.2
  let T := SheafOfModules.overFunctor.{u} (localCoefficientRings R) U
  let M₀ := DerivedCategory.Q.objPreimage K
  let M := (T.mapHomologicalComplex (.up ℤ)).obj M₀
  let c := T.mapDerivedCategoryFactors
  let r := DerivedCategory.Q.objObjPreimageIso K
  let F := localCoefficientDerivedRestriction R U
  let β := localSectionDerivedMultiplication R U f
  have hbase : DerivedCategory.Q.map (sectionComplexMultiplication R U f M) ≫
      c.inv.app M₀ = c.inv.app M₀ ≫ β.app (DerivedCategory.Q.obj M₀) := by
    dsimp only [β, localSectionDerivedMultiplication]
    rw [Localization.liftNatTrans_app]
    change DerivedCategory.Q.map (sectionComplexMultiplication R U f M) ≫ c.inv.app M₀ =
      c.inv.app M₀ ≫ (c.hom.app M₀ ≫ _ ≫ c.inv.app M₀)
    simp only [Iso.inv_hom_id_app_assoc]
    rfl
  have hnat := β.naturality r.hom
  change DerivedCategory.Q.map (sectionComplexMultiplication R U f M) ≫
      (c.inv.app M₀ ≫ F.map r.hom) = (c.inv.app M₀ ≫ F.map r.hom) ≫ β.app K
  calc
    _ = (DerivedCategory.Q.map (sectionComplexMultiplication R U f M) ≫
        c.inv.app M₀) ≫ F.map r.hom := (Category.assoc _ _ _).symm
    _ = (c.inv.app M₀ ≫ β.app (DerivedCategory.Q.obj M₀)) ≫ F.map r.hom :=
      congrArg (fun x ↦ x ≫ F.map r.hom) hbase
    _ = c.inv.app M₀ ≫ (β.app (DerivedCategory.Q.obj M₀) ≫ F.map r.hom) :=
      Category.assoc _ _ _
    _ = c.inv.app M₀ ≫ (F.map r.hom ≫ β.app K) :=
      congrArg (fun x ↦ c.inv.app M₀ ≫ x) hnat.symm
    _ = _ := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_scalar
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    (M : ringedSiteModules.{u} ((localCoefficientRings R).over U)) :
    SheafOfModules.homObjMap (R := R.over U)
        (localSectionMultiplication R U f (SheafOfModules.unit _)) (𝟙 M) ≫
        (SheafOfModules.homObjUnitIso (R := R.over U) M).hom =
      (SheafOfModules.homObjUnitIso (R := R.over U) M).hom ≫
        localSectionMultiplication R U f M := by
  apply SheafOfModules.hom_ext
  ext V φ : 3
  change (φ.app (op (Over.mk (𝟙 V.unop)))).hom
      ((localSectionMultiplication R U f (SheafOfModules.unit _)).val.app V
        (1 : (R.over U).obj.obj V)) =
    ((localSectionMultiplication R U f M).val.app V).hom
      ((φ.app (op (Over.mk (𝟙 V.unop)))).hom (1 : (R.over U).obj.obj V))
  let a : (R.over U).obj.obj V := R.obj.map V.unop.hom.op f
  change (φ.app (op (Over.mk (𝟙 V.unop)))).hom (a • (1 : (R.over U).obj.obj V)) =
    a • (φ.app (op (Over.mk (𝟙 V.unop)))).hom (1 : (R.over U).obj.obj V)
  exact (φ.app (op (Over.mk (𝟙 V.unop)))).hom.map_smul a (1 : (R.over U).obj.obj V)

/-- Internal derived Hom sends the free telescope endomorphism to the Roos
endomorphism on the product of copies of the restricted target.

Source: Stacks Project, Tag 0997, proof of lemma-hom-from-Af, (1) equivalent to (3).
(auxiliary; not a blueprint node).

Proof:
1. On the slice choose a K-injective complex I representing the restricted target L.
Compute derived internal Hom from the free sum in degree zero as Hom-complex(P[0],I).
2. In each degree only the source degree zero contributes. A local map from the free
sum is determined by its restrictions to all unit summands. Evaluation at one identifies
these restrictions with the sections of I. This gives a chain isomorphism from the Hom
complex to the termwise product of copies of I, with its actual coordinate projections.
3. The product of K-injectives represents the derived product with those projections.
Compose with the representative isomorphism Q(I) ≅ L to obtain the asserted isomorphism.
4. Precomposition with identity minus the f-weighted forward shift sends a family x to
(x_n - f*x_(n+1))_n. Naturality of evaluation at one, of the K-injective comparison, and
of the derived restriction comparison identifies the scalar on Q(I) with the specified
localSectionDerivedMultiplication. Equality follows by the product's projection extensionality.
This uses no exactness of products of sheaves. -/
theorem localCoefficientTelescope_rhom_product
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u} (localCoefficientRings R)))
    [HasProduct (fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)] :
    let L := (localCoefficientDerivedRestriction R U).obj K
    let S := DerivedCategory.singleFunctor
      (ringedSiteModules.{u} ((localCoefficientRings R).over U)) 0
    let H := (Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj L
    ∃ e : H.obj (op (S.obj (localCoefficientFree R U))) ≅ ∏ᶜ (fun _ : ℕ ↦ L),
      H.map (S.map (localCoefficientTelescopeMap R U f)).op ≫ e.hom =
        e.hom ≫ towerTransitionEndomorphism
          (K := fun _ : ℕ ↦ L) (fun _ ↦ (localSectionDerivedMultiplication R U f).app K) := by
  classical
  let A := ringedSiteModules.{u} ((localCoefficientRings R).over U)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let L := (localCoefficientDerivedRestriction R U).obj K
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let hI := fun M ↦
    And.intro (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2
      (CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M)
  let M := (restrictionRepresentative R U K).1
  let eL := (restrictionRepresentative R U K).2
  let I := I₀.obj M
  have : QuasiIso (η.app M) := (hI M).1
  let eI : DerivedCategory.Q.obj I ≅ L :=
    (asIso (DerivedCategory.Q.map (η.app M))).symm ≪≫ eL
  let b := localSectionMultiplication R U f (SheafOfModules.unit _)
  let t := sectionComplexMultiplication R U f I
  let β := (localSectionDerivedMultiplication R U f).app K
  have hβ : DerivedCategory.Q.map t ≫ eI.hom = eI.hom ≫ β := by
    apply (cancel_epi (DerivedCategory.Q.map (η.app M))).1
    change DerivedCategory.Q.map (η.app M) ≫
        (DerivedCategory.Q.map t ≫ (inv (DerivedCategory.Q.map (η.app M)) ≫ eL.hom)) =
      DerivedCategory.Q.map (η.app M) ≫
        ((inv (DerivedCategory.Q.map (η.app M)) ≫ eL.hom) ≫ β)
    rw [← Category.assoc (DerivedCategory.Q.map (η.app M)), ← Functor.map_comp,
      sectionComplexMultiplication_naturality, Functor.map_comp]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact restrictionRepresentative_scalar R U f K
  let G := SheafOfModules.homFunctor (R.over U)
  let F := homComplexFunctor.{u, u, u, u} (R := R.over U)
  let π := chosenProjections (R.over U)
  let ev := unitEvaluationIso (R.over U)
  let ν := fun N ↦ SheafOfModules.homObjUnitIso (R := R.over U) N
  have hmap (L L' M M' : CochainComplex A ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (h : p + n = q) :
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q h =
        π L M n p q h ≫ abstractHomMap G (f.f p) (g.f q) := by
    rw [abstractHomMap_sheaf]
    exact (Classical.choose_spec (homComplex_projections_exists.{u, u, u, u} (R := R.over U))).2.2
      L L' M M' f g n p q h
  have hFan := abstractFreeHomFan_isLimit G (unitModule (R.over U)) ν F π
    (Classical.choose_spec (homComplex_projections_exists.{u, u, u, u} (R := R.over U))).1 hmap
    ev (unitEvaluation_f (R.over U)) I (fun k ↦ by
      change IsLimit (Fan.mk
        (SheafOfModules.homObj (R := R.over U) (freeUnit (R.over U)) (I.X k))
        (fun n : ℕ ↦ abstractHomMap G
          (Sigma.ι (fun _ : ℕ ↦ unitModule (R.over U)) n) (𝟙 (I.X k))))
      simp only [G, abstractHomMap_sheaf]
      exact (SheafOfModules.internalHomCoproductFanIsLimit (R.over U)
        (fun _ : ℕ ↦ unitModule (R.over U)) (Cofan.mk (freeUnit (R.over U))
          (Sigma.ι (fun _ : ℕ ↦ unitModule (R.over U))))
        (coproductIsCoproduct (fun _ : ℕ ↦ unitModule (R.over U))) (I.X k)).some)
  have heval := abstractEvaluation_scalar G (unitModule (R.over U)) ν F π hmap ev
    (unitEvaluation_f (R.over U)) I b t (fun n ↦ by
      rw [abstractHomMap_sheaf]
      exact evaluation_scalar R U f (I.X n))
  obtain ⟨z, ⟨hc⟩, hz⟩ := rhomFreeFan_isLimit (R.over U) I₀ η hI M L eL eI b t β
    ev hFan heval hβ
  let S := DerivedCategory.singleFunctor A 0
  let H := (Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj L
  obtain ⟨hshift, htri⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 L
  let := hshift
  let := htri
  exact dualTelescope S H (SheafOfModules.unit _) b (localCoefficientTelescopeMap R U f)
    (fun n ↦ by simp [localCoefficientTelescopeMap, b]) L β z hc hz

end CategoryTheory
