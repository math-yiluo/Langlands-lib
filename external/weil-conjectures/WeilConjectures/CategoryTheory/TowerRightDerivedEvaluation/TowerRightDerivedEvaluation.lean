/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Unbounded right derivation commutes with tower evaluation

Source: Stacks Project, Sites Cohomology, Tag 0941, proof of
`lemma-derived-limit-is-ok`, and Derived Categories, Tags 070I, 070Y and 070K;
additive-functor generalization (blueprint: lem-coef-tower-right-derived-evaluation).

The units and resolution comparisons are those of
`Functor.rightDerivedFunctorOfQuasiIsoResolutions`. Natural number `n` denotes positive
level `n + 1`. No exactness or adjunction assumption is imposed on the additive functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TowerRightDerivedEvaluation

/-- The cochain realization of the universal unit for arbitrary quasi-isomorphism
K-injective resolutions, using the canonical quotient/localization comparisons.
Source: Stacks Project, Derived Categories, Tags 070K and 070Y
(blueprint: lem-coef-tower-right-derived-evaluation). -/
def cochainUnit
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive]
    (enough : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (P : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (F.rightDerivedFunctorOfQuasiIsoResolutions enough).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit enough).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutions enough).map
      ((DerivedCategory.quotientCompQhIso A).hom.app P)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private def unitNatTrans
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive]
    (enough : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a) :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions enough :=
  Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso B).inv ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit enough) ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom
      (F.rightDerivedFunctorOfQuasiIsoResolutions enough)

private theorem unit_isIso
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive]
    (enough : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (cochainUnit F enough I) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough I
  unfold cochainUnit
  infer_instance

/-- Descend a comparison invertible on K-injectives, using the Hom bijection of
Stacks Tag 070I. Naturality along a resolution gives normalization on all complexes. -/
private theorem descend_comparison
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    [Abelian C] [HasDerivedCategory.{wA} C]
    (enough : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (R S : DerivedCategory C ⥤ D) (H : CochainComplex C ℤ ⥤ D)
    (a : H ⟶ DerivedCategory.Q ⋙ R) (b : H ⟶ DerivedCategory.Q ⋙ S)
    (ha : ∀ I : CochainComplex C ℤ, I.IsKInjective → IsIso (a.app I))
    (hb : ∀ I : CochainComplex C ℤ, I.IsKInjective → IsIso (b.app I)) :
    ∃ β : R ≅ S, ∀ K : CochainComplex C ℤ,
      a.app K ≫ β.hom.app (DerivedCategory.Q.obj K) = b.app K := by
  classical
  let π := HomotopyCategory.quotient C (.up ℤ)
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let d (I : CochainComplex C ℤ) (hI : I.IsKInjective) :
      R.obj (Q.obj I) ⟶ S.obj (Q.obj I) :=
    letI := ha I hI
    inv (a.app I) ≫ b.app I
  have dn (I J : CochainComplex C ℤ) (hI : I.IsKInjective) (hJ : J.IsKInjective)
      (f : I ⟶ J) :
      R.map (Q.map f) ≫ d J hJ = d I hI ≫ S.map (Q.map f) := by
    have := ha I hI
    have := ha J hJ
    apply (cancel_epi (a.app I)).mp
    change a.app I ≫ (R.map (Q.map f) ≫ (inv (a.app J) ≫ b.app J)) =
      a.app I ≫ ((inv (a.app I) ≫ b.app I) ≫ S.map (Q.map f))
    have an := a.naturality f
    dsimp only [Functor.comp_map] at an
    rw [← Category.assoc, ← an]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact b.naturality f
  have dn' (I J : CochainComplex C ℤ) (hI : I.IsKInjective) (hJ : J.IsKInjective)
      (f : Q.obj I ⟶ Q.obj J) :
      R.map f ≫ d J hJ = d I hI ≫ S.map f := by
    let q := DerivedCategory.quotientCompQhIso C
    obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (π.obj I) J).surjective
      (q.hom.app I ≫ f ≫ q.inv.app J)
    obtain ⟨g, rfl⟩ := π.map_surjective g
    have hgf : Q.map g = f := by
      have hn := q.hom.naturality g
      change DerivedCategory.Qh.map (π.map g) ≫ q.hom.app J =
        q.hom.app I ≫ Q.map g at hn
      rw [hg] at hn
      simp only [Category.assoc] at hn
      erw [Iso.inv_hom_id_app, Category.comp_id] at hn
      exact (cancel_epi (q.hom.app I)).mp hn.symm
    rw [← hgf]
    exact dn I J hI hJ g
  choose J f hJ hf using fun K ↦ enough K
  let j (X : DerivedCategory C) := J (Q.objPreimage X)
  have hj (X : DerivedCategory C) : (j X).IsKInjective := hJ _
  have hq (K : CochainComplex C ℤ) : IsIso (Q.map (f K)) := by
    have := hf K
    infer_instance
  let e (X : DerivedCategory C) : X ≅ Q.obj (j X) :=
    (Q.objObjPreimageIso X).symm ≪≫ asIso (Q.map (f (Q.objPreimage X)))
  let c (X : DerivedCategory C) := R.map (e X).hom ≫ d (j X) (hj X) ≫ S.map (e X).inv
  have cn {X Y : DerivedCategory C} (f : X ⟶ Y) :
      R.map f ≫ c Y = c X ≫ S.map f := by
    have ht := dn' (j X) (j Y) (hj X) (hj Y) ((e X).inv ≫ f ≫ (e Y).hom)
    have ht' := congrArg (fun t ↦ R.map (e X).hom ≫ t ≫ S.map (e Y).inv) ht
    simpa only [c, Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc,
      Iso.inv_hom_id_map_assoc, Iso.hom_inv_id_map, Category.comp_id] using ht'
  have ci (X : DerivedCategory C) : IsIso (c X) := by
    have := ha (j X) (hj X)
    have := hb (j X) (hj X)
    dsimp only [c, d]
    infer_instance
  let β : R ≅ S := NatIso.ofComponents (fun X ↦ asIso (c X)) (fun f ↦ cn f)
  have atI (I : CochainComplex C ℤ) (hI : I.IsKInjective) :
      β.hom.app (Q.obj I) = d I hI := by
    have ht := dn' (j (Q.obj I)) I (hj _) hI (e (Q.obj I)).inv
    have ht' := congrArg (fun t ↦ R.map (e (Q.obj I)).hom ≫ t) ht
    change c (Q.obj I) = _
    simpa only [c, Category.assoc, Iso.hom_inv_id_map_assoc] using ht'.symm
  refine ⟨β, ?_⟩
  intro K
  obtain ⟨I, f, hI, hf⟩ := enough K
  have := ha I hI
  have hnorm : a.app I ≫ β.hom.app (Q.obj I) = b.app I := by
    rw [atI I hI]
    exact IsIso.hom_inv_id_assoc _ _
  apply (cancel_mono (S.map (Q.map f))).mp
  rw [Category.assoc, ← β.hom.naturality, ← Category.assoc]
  have an := a.naturality f
  dsimp only [Functor.comp_map] at an
  rw [← an]
  rw [Category.assoc, hnorm]
  exact b.naturality f

/-- Cancel the inverse unit in the canonical resolution comparison (Stacks Tag 070Y). -/
private theorem resolution_unit
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive]
    (enough : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {P I : CochainComplex A ℤ} [I.IsKInjective] (a : P ⟶ I) [QuasiIso a] :
    (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough a).hom ≫
        cochainUnit F enough I =
      (F.rightDerivedFunctorOfQuasiIsoResolutions enough).map (DerivedCategory.Q.map a) := by
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough I
  have hid : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app I = 𝟙 _ := rfl
  simp [Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso, cochainUnit, hid,
    Category.assoc, ← Functor.map_comp]

private theorem derived_ext
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    [Abelian C] [HasDerivedCategory.{wA} C]
    (enough : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {R S : DerivedCategory C ⥤ D} (α β : R ⟶ S)
    (h : ∀ I : CochainComplex C ℤ, I.IsKInjective →
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  obtain ⟨I, f, hI, hf⟩ := enough K
  apply (cancel_mono (S.map (DerivedCategory.Q.map f))).mp
  rw [← α.naturality, ← β.naturality, h I hI]

private theorem towerTransition_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J =
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) := by
  have hm : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj m).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors := rfl
  have hn : Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
      (((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory =
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors := rfl
  simp [towerDerivedEvaluationTransition, Localization.liftNatTrans_app, hm, hn]

private theorem towerTransition_inv_fac
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    {m n : ℕᵒᵖ} (t : m ⟶ n) (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.inv.app J ≫
        (towerDerivedEvaluationTransition A t).app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app J) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.inv.app J := by
  apply (cancel_mono
    (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app J)).mp
  simp only [Category.assoc, towerTransition_fac, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

/-- Unbounded right derivation of an additive termwise tower functor commutes with
exact evaluation, with its universal units, every K-injective resolution and every
actual tower transition. The resolution equation identifies both sides with Q(F(I_n));
since it holds for every resolution and the same natural isomorphism, it includes
resolution independence and naturality for all derived morphisms.
Source: Stacks Project, Sites Cohomology, Tag 0941, exact-left-adjoint paragraph;
Derived Categories, Tags 070I, 070Y and 070K; additive-functor generalization
(blueprint: lem-coef-tower-right-derived-evaluation).

Proof:
1. Use the universal derived pairs of `def-sfb-right-derived-functor`. The two
   exact evaluation factors and their cochain units give natural transformations
   a and b with the same source, since termwise F commutes strictly with evaluation.
2. Both transformations are invertible on K-injective towers: the derived units
   are invertible there and `lem-weil-tower-evaluation-kinjective` applies to b.
   Define the comparison on such a tower by a inverse followed by b.
3. By `lem-weil-pbc-kinjective-hom-derived`, every derived morphism between
   K-injective towers comes from a homotopy class and hence a complex map.
   Naturality of a and b proves naturality of the comparison on these morphisms.
   Resolve a representative of each derived object and conjugate the comparison
   by its resolution isomorphism. Naturality also proves agreement with every
   K-injective representative. Naturality along any resolution gives a beta = b
   on all complexes, which is exactly the asserted unit equation.
4. Unfold the canonical resolution comparison to obtain c_f eta_I = RF(Qf).
   Postcompose the desired resolution equation with the invertible evaluated
   unit. Naturality of beta and the exact evaluation factor, followed by the
   unit equation at I, identifies both sides with evaluation of RT(Qf).
5. The localized transition conjugated by the evaluation factors is Q of the
   actual transition of complexes. Naturality of the units therefore gives the
   same transition map on the sources of a and b. Cancel a on K-injective
   towers to prove transition compatibility there. Naturality along a resolution
   extends this equality to every derived object.
-/
theorem exists_normalized
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive]
    (enough : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enoughT : ∀ K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a) :
    ∃ β : ∀ n : ℕᵒᵖ,
      (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).rightDerivedFunctorOfQuasiIsoResolutions
          enoughT) ⋙ ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ≅
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ⋙
          F.rightDerivedFunctorOfQuasiIsoResolutions enough,
      (∀ (n : ℕᵒᵖ) (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
        ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.inv.app
              ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
                (.up ℤ)).obj P) ≫
            ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
              (cochainUnit ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) enoughT P) ≫
            (β n).hom.app (DerivedCategory.Q.obj P) ≫
            (F.rightDerivedFunctorOfQuasiIsoResolutions enough).map
              (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app P) =
          cochainUnit F enough
            ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ (n : ℕᵒᵖ) (P I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (a : P ⟶ I)
          [I.IsKInjective] [QuasiIso a],
        ∃ (hI : CochainComplex.IsKInjective
              ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I))
          (ha : QuasiIso
              ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map a)),
          (β n).hom.app (DerivedCategory.Q.obj P) ≫
              (F.rightDerivedFunctorOfQuasiIsoResolutions enough).map
                (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app P) ≫
              (@Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
                A B _ _ _ _ _ _ F _ enough _ _ hI
                ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map a) ha).hom =
            ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
                (Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
                  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) enoughT a).hom ≫
              ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app
                ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
                  (.up ℤ)).obj I)) ∧
      (∀ (m n : ℕᵒᵖ) (t : m ⟶ n) (M : DerivedCategory (ℕᵒᵖ ⥤ A)),
        (towerDerivedEvaluationTransition B t).app
              ((Functor.rightDerivedFunctorOfQuasiIsoResolutions
                ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) enoughT).obj M) ≫
            (β n).hom.app M =
          (β m).hom.app M ≫ (F.rightDerivedFunctorOfQuasiIsoResolutions enough).map
            ((towerDerivedEvaluationTransition A t).app M)) := by
  classical
  let FT := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
  let R := F.rightDerivedFunctorOfQuasiIsoResolutions enough
  let RT := FT.rightDerivedFunctorOfQuasiIsoResolutions enoughT
  let η := unitNatTrans F enough
  let ηT := unitNatTrans FT enoughT
  let FTc := FT.mapHomologicalComplex (.up ℤ)
  let EA (n : ℕᵒᵖ) := (evaluation ℕᵒᵖ A).obj n
  let EB (n : ℕᵒᵖ) := (evaluation ℕᵒᵖ B).obj n
  let a (n : ℕᵒᵖ) : FTc ⋙ (EB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RT ⋙ (EB n).mapDerivedCategory :=
    Functor.whiskerLeft FTc (EB n).mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight ηT (EB n).mapDerivedCategory
  let b (n : ℕᵒᵖ) : FTc ⋙ (EB n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (EA n).mapDerivedCategory ⋙ R :=
    Functor.whiskerLeft ((EA n).mapHomologicalComplex (.up ℤ)) η ≫
      Functor.whiskerRight (EA n).mapDerivedCategoryFactors.inv R
  have ha (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective) :
      IsIso ((a n).app I) := by
    have := unit_isIso FT enoughT I
    change IsIso ((EB n).mapDerivedCategoryFactors.inv.app (FTc.obj I) ≫
      (EB n).mapDerivedCategory.map (cochainUnit FT enoughT I))
    infer_instance
  have hb (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : I.IsKInjective) :
      IsIso ((b n).app I) := by
    have : CochainComplex.IsKInjective
        (((EA n).mapHomologicalComplex (.up ℤ)).obj I) :=
      tower_evaluation_isKInjective A I n
    have := unit_isIso F enough (((EA n).mapHomologicalComplex (.up ℤ)).obj I)
    change IsIso (cochainUnit F enough (((EA n).mapHomologicalComplex (.up ℤ)).obj I) ≫
      R.map ((EA n).mapDerivedCategoryFactors.inv.app I))
    infer_instance
  have ex (n : ℕᵒᵖ) := descend_comparison enoughT
    (RT ⋙ (EB n).mapDerivedCategory) ((EA n).mapDerivedCategory ⋙ R)
    _ (a n) (b n) (ha n) (hb n)
  choose β hβ using ex
  have hn (n : ℕᵒᵖ) (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      (EB n).mapDerivedCategoryFactors.inv.app (FTc.obj P) ≫
        (EB n).mapDerivedCategory.map (cochainUnit FT enoughT P) ≫
        (β n).hom.app (DerivedCategory.Q.obj P) ≫
        R.map ((EA n).mapDerivedCategoryFactors.hom.app P) =
      cochainUnit F enough (((EA n).mapHomologicalComplex (.up ℤ)).obj P) := by
    have h := congrArg
      (fun f ↦ f ≫ R.map ((EA n).mapDerivedCategoryFactors.hom.app P)) (hβ n P)
    dsimp only [a, b, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app] at h
    simp only [Category.assoc, ← R.map_comp, Iso.inv_hom_id_app, R.map_id] at h
    erw [Category.comp_id] at h
    exact h
  refine ⟨β, hn, ?_, ?_⟩
  · intro n P I f hI hf
    have hE : CochainComplex.IsKInjective
        (((EA n).mapHomologicalComplex (.up ℤ)).obj I) :=
      tower_evaluation_isKInjective A I n
    have hq : QuasiIso (((EA n).mapHomologicalComplex (.up ℤ)).map f) := inferInstance
    refine ⟨hE, hq, ?_⟩
    have := unit_isIso F enough (((EA n).mapHomologicalComplex (.up ℤ)).obj I)
    have hu : (EB n).mapDerivedCategory.map (cochainUnit FT enoughT I) ≫
        (β n).hom.app (DerivedCategory.Q.obj I) ≫
        R.map ((EA n).mapDerivedCategoryFactors.hom.app I) =
      (EB n).mapDerivedCategoryFactors.hom.app (FTc.obj I) ≫
        cochainUnit F enough (((EA n).mapHomologicalComplex (.up ℤ)).obj I) := by
      apply (cancel_epi ((EB n).mapDerivedCategoryFactors.inv.app (FTc.obj I))).mp
      simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hn n I
    apply (cancel_mono
      (cochainUnit F enough (((EA n).mapHomologicalComplex (.up ℤ)).obj I))).mp
    simp only [Category.assoc]
    rw [resolution_unit F enough (((EA n).mapHomologicalComplex (.up ℤ)).map f)]
    erw [← R.map_comp, ← (EA n).mapDerivedCategoryFactors.hom.naturality f, R.map_comp]
    erw [← Category.assoc, ← (β n).hom.naturality (DerivedCategory.Q.map f)]
    dsimp only [Functor.comp_map]
    erw [← hu, ← (EB n).mapDerivedCategory.map_comp_assoc,
      resolution_unit FT enoughT f]
    exact Category.assoc _ _ _
  · intro m n t M
    let sA := towerDerivedEvaluationTransition A t
    let sB := towerDerivedEvaluationTransition B t
    have heq : Functor.whiskerLeft RT sB ≫ (β n).hom =
        (β m).hom ≫ Functor.whiskerRight sA R := by
      apply derived_ext enoughT
      intro I hI
      let u := DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app I))
      have hna : (a m).app I ≫ sB.app (RT.obj (DerivedCategory.Q.obj I)) =
          u ≫ (a n).app I := by
        change ((EB m).mapDerivedCategoryFactors.inv.app (FTc.obj I) ≫
          (EB m).mapDerivedCategory.map (cochainUnit FT enoughT I)) ≫ sB.app _ = _
        rw [Category.assoc, sB.naturality, ← Category.assoc]
        rw [towerTransition_inv_fac, Category.assoc]
        rfl
      have hnb : (b m).app I ≫ R.map (sA.app (DerivedCategory.Q.obj I)) =
          u ≫ (b n).app I := by
        change (cochainUnit F enough (((EA m).mapHomologicalComplex (.up ℤ)).obj I) ≫
          R.map ((EA m).mapDerivedCategoryFactors.inv.app I)) ≫ R.map _ = _
        erw [Category.assoc, ← R.map_comp, towerTransition_inv_fac, R.map_comp]
        erw [← Category.assoc, ← η.naturality, Category.assoc]
        rfl
      have := ha m I hI
      change sB.app _ ≫ (β n).hom.app _ = (β m).hom.app _ ≫ R.map (sA.app _)
      apply (cancel_epi ((a m).app I)).mp
      rw [← Category.assoc, hna, Category.assoc, hβ n I]
      rw [← Category.assoc, hβ m I]
      exact hnb.symm
    exact NatTrans.congr_app heq M

end CategoryTheory.TowerRightDerivedEvaluation
