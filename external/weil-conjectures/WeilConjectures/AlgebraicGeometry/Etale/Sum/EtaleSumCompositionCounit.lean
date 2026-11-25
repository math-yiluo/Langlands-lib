/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing

import Mathlib.CategoryTheory.Localization.Predicate

/-! # Evaluation and composition of exact etale sum adjunctions

Source: Stacks Project, Etale Cohomology, Tags 03S3 and 03S5; More on Etale
Cohomology, Tag 0F50 (blueprint: lem-pur-etale-sum-composition-counit).

The sum compositor is constructed on sheaves from the universal property of sum extension
against literal restriction along the small-site localization functors. It is then descended
termwise. Thus its construction specifies the nested-summand comparison independently of
the derived pullback compositor whose conjugacy is asserted below.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

open CategoryTheory.ExactDerivedPasting

private lemma ofNatIsoRight_trans
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R S T : D ⥤ C}
    (a : L ⊣ R) (e : R ≅ S) (f : S ≅ T) :
    (a.ofNatIsoRight e).ofNatIsoRight f = a.ofNatIsoRight (e ≪≫ f) := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext X
  simp [Adjunction.ofNatIsoRight_unit, Category.assoc]

private lemma comp_ofNatIsoRight
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ : C ⥤ D} {R₁ S₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ S₂ : E ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e₁ : R₁ ≅ S₁) (e₂ : R₂ ≅ S₂) :
    (a₁.ofNatIsoRight e₁).comp (a₂.ofNatIsoRight e₂) =
      (a₁.comp a₂).ofNatIsoRight
        (Functor.isoWhiskerRight e₂ R₁ ≪≫ Functor.isoWhiskerLeft S₂ e₁) := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext X
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.map_comp, Category.assoc]
  rw [← e₁.hom.naturality_assoc, ← e₁.hom.naturality]
  rfl

private lemma conjugate_of_counit
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (s : L₂ ⟶ L₁) (k : R₁ ⟶ R₂)
    (h : ∀ Y, s.app (R₁.obj Y) ≫ a₁.counit.app Y =
      L₂.map (k.app Y) ≫ a₂.counit.app Y) :
    conjugateEquiv a₁ a₂ s = k := by
  apply NatTrans.ext
  funext Y
  simp only [conjugateEquiv_apply_app, ← Functor.map_comp]
  rw [h, Functor.map_comp, a₂.unit_naturality_assoc,
    a₂.right_triangle_components]
  simp

private lemma cell_iso
    {I : Type*} (C : I → Type*) [∀ i, Category (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory (C i)] {i j : I} {P R : Word C i j}
    (alpha : P.ordinary.obj ≅ R.ordinary.obj) :
    Word.cell C alpha.hom = P.comparison.inv ≫
      (Functor.mapDerivedCategoryNatIso alpha).hom ≫ R.comparison.hom := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma cell_counit
    {I : Type*} (C : I → Type*) [∀ i, Category (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory (C i)] {i j : I}
    (L : C i ⥤ C j) (R : C j ⥤ C i)
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R) :
    Word.cell C (P := .comp (.edge (ExactFunctor.of R)) (.edge (ExactFunctor.of L)))
      (R := .nil j) adj.counit = adj.onDerivedCategory.counit := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (C j) (.up ℤ))
  intro K
  dsimp only [Word.cell, Word.comparison, Word.ordinary]
  simp only [Iso.trans_refl, Functor.isoWhiskerLeft_refl,
    Functor.isoWhiskerRight_refl, NatTrans.comp_app]
  rw [Localization.liftNatTrans_app, Functor.mapDerivedCategoryIdIso_hom_app_Q_obj]
  change (Functor.mapDerivedCategoryCompIso R L).hom.app (DerivedCategory.Q.obj K) ≫
      ((R ⋙ L).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app K) ≫
        (𝟭 (C j)).mapDerivedCategoryFactors.inv.app K) ≫
      (𝟭 (C j)).mapDerivedCategoryFactors.hom.app K = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors R L K,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [Adjunction.onDerivedCategory, Adjunction.localization_counit_app,
    Category.assoc]
  erw [Category.comp_id]
  rfl

/-- Literal restriction composes by composition of the small-site localization functors.
Source: Stacks Tag 03S3, restriction description preceding equation-j-p-shriek
(blueprint: lem-pur-etale-sum-composition-counit). -/
noncomputable def etaleSumRestrictionCompIso
    (A : Type (u + 1)) [CommRing A]
    {U X T : Scheme.{u}} (e : U ⟶ X) (v : X ⟶ T) [Etale e] [Etale v] :
    localizationRestriction (ModuleCat.{u + 1} A) v inferInstance ⋙
        localizationRestriction (ModuleCat.{u + 1} A) e inferInstance ≅
      localizationRestriction (ModuleCat.{u + 1} A) (e ≫ v) inferInstance :=
  Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale e)
      (inferInstance : Etale v)).symm (ModuleCat.{u + 1} A)
    (U.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)

/-- The sheaf sum compositor: the universal map identifying two successive sums with the
sum over composite lifts. The restriction comparison is induced by `Over.mapComp`; the
left-adjoint uniqueness construction therefore sends each nested generator to its composite
lift generator, including the intervening sheafification.
Source: Stacks Tags 03S3 (equation-j-p-shriek) and 0F50
(blueprint: lem-pur-etale-sum-composition-counit). -/
noncomputable def etaleSumSheafCompIso
    (A : Type (u + 1)) [CommRing A]
    {U X T : Scheme.{u}} (e : U ⟶ X) (v : X ⟶ T) [Etale e] [Etale v] :
    etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ≅
      etaleLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) inferInstance :=
  (((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).comp
      (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v)).ofNatIsoRight
        (etaleSumRestrictionCompIso A e v)).leftAdjointUniq
    (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) (e ≫ v))

/-- The sum compositor sends a nested structural summand to the summand for its
composite lift. The units here are the structural inclusions into sheafified sums; the
last restriction transports along the literal small-site composition isomorphism.
Source: Stacks Tags 03S3 and 0F50; the final etale clause of
lem-sfb-quasifinite-compact-support-exact
(blueprint: lem-pur-etale-sum-composition-counit).

Proof: Transpose the sheaf sum compositor across the composite restriction adjunction.
By the defining left-adjoint uniqueness property this is the unit of the single sum
adjunction. The composite unit is the two successive structural summand inclusions;
evaluating it on W gives the displayed equation. The restriction comparison is induced
by Over.mapComp, which accounts for the last restriction. Thus the comparison has exactly
the nested-summand normalization specified by lem-sfb-quasifinite-compact-support-exact. -/
theorem etaleSumSheafCompIso_summand
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale) :
    ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app M).hom.app
        (Opposite.op W) ≫
      ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v).unit.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)).hom.app
          (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) ≫
      ((etaleSumSheafCompIso A e v).hom.app M).hom.app
        (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))) =
    ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A)
        (e ≫ v)).unit.app M).hom.app (Opposite.op W) ≫
      ((etaleLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) inferInstance).obj M).obj.map
        ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale e)
          (inferInstance : Etale v)).inv.app W).op := by
  let adj := (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).comp
    (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v)
  let rho := etaleSumRestrictionCompIso A e v
  have h := (adj.ofNatIsoRight rho).homEquiv_leftAdjointUniq_hom_app
    (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) (e ≫ v)) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
  have h' := (Iso.eq_comp_inv (rho.app _)).2 h
  have hh := congrArg (fun f ↦ f.hom.app (Opposite.op W)) h'
  simpa [adj, rho, etaleSumSheafCompIso, etaleSumRestrictionCompIso,
    Adjunction.comp_unit_app, localizationRestriction,
    Functor.sheafPushforwardContinuous] using hh

set_option backward.isDefEq.respectTransparency false in
private lemma sheaf_composition_counit
    (A : Type (u + 1)) [CommRing A]
    {U X T : Scheme.{u}} (e : U ⟶ X) (v : X ⟶ T) [Etale e] [Etale v]
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleSumSheafCompIso A e v).hom.app
        ((upperStar (ModuleCat.{u + 1} A) (e ≫ v)).obj N) ≫
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (e ≫ v)
        inferInstance).counit.app N =
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).map
          ((upperStarComp (ModuleCat.{u + 1} A) e v).hom.app N) ≫
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance |>.comp
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)).counit.app
          N := by
  let L := etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
    etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance
  let rho := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) (e ≫ v)
    inferInstance
  let a := ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).comp
    (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v)).ofNatIsoRight
      (etaleSumRestrictionCompIso A e v)
  have h := a.leftAdjointUniq_hom_app_counit
    (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) (e ≫ v)) N
  have hh := congrArg (L.map (rho.hom.app N) ≫ ·) h
  change L.map (rho.hom.app N) ≫ (etaleSumSheafCompIso A e v).hom.app _ ≫
    (etaleLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) inferInstance).map (rho.inv.app N) ≫
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (e ≫ v)
        inferInstance).counit.app N = _ at hh
  rw [(etaleSumSheafCompIso A e v).hom.naturality_assoc] at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp] at hh
  rw [hh]
  let ae := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance
  let av := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance
  let re := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e inferInstance
  let rv := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) v inferInstance
  let tau := Functor.isoWhiskerRight rv (upperStar (ModuleCat.{u + 1} A) e) ≪≫
    Functor.isoWhiskerLeft (localizationRestriction (ModuleCat.{u + 1} A) v inferInstance) re
  let kappa := upperStarComp (ModuleCat.{u + 1} A) e v
  let c := etaleSumRestrictionCompIso A e v
  have ht : tau ≪≫ c = kappa.symm ≪≫ rho := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (cancel_epi (kappa.hom.app M)).1
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Iso.hom_inv_id_app_assoc]
    have hm : kappa.hom.app M ≫ tau.hom.app M = rho.hom.app M ≫ c.inv.app M :=
      congr_app (upperStarComp_hom_comp_upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} A) e v inferInstance inferInstance (e ≫ v) rfl inferInstance) M
    rw [← Category.assoc, hm]
    simp
  have ha : a = (ae.comp av).ofNatIsoRight (kappa.symm ≪≫ rho) := by
    change ((ae.ofNatIsoRight re).comp (av.ofNatIsoRight rv)).ofNatIsoRight c = _
    rw [comp_ofNatIsoRight, ofNatIsoRight_trans]
    exact congrArg ((ae.comp av).ofNatIsoRight) ht
  rw [ha]
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.trans_inv, Iso.symm_inv, Functor.map_comp,
    Category.assoc]
  rw [← L.map_comp_assoc, Iso.hom_inv_id_app, L.map_id, Category.id_comp]

/-- The specified degreewise sum-composition comparison on ordinary unbounded categories.
Source: Stacks Tags 03S3 and 0F50; exact-functor localization
(blueprint: lem-pur-etale-sum-composition-counit). -/
noncomputable def derivedEtaleSumCompIso
    (A : Type (u + 1)) [CommRing A]
    {U X T : Scheme.{u}} (e : U ⟶ X) (v : X ⟶ T) [Etale e] [Etale v] :
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) inferInstance).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (etaleSumSheafCompIso A e v)

attribute [local irreducible] upperStar etaleLowerShriek Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- The specified derived nested-sum compositor preserves the evaluation counit, and its
adjunction conjugate is the canonical exact pullback-composition comparison.
Source: Stacks Tags 03S3, 03S5 and 0F50
(blueprint: lem-pur-etale-sum-composition-counit).

Proof:
1. Left-adjoint uniqueness identifies the sum compositor with the comparison between the
   composite restriction adjunction and the single restriction adjunction. Its counit
   equation follows from leftAdjointUniq_hom_app_counit.
2. Transport these adjunctions along the canonical pullback/restriction comparisons.
   Their compatibility with upperStarComp, proved in HeartGluing, turns that counit
   equation into the sheaf composition equation.
3. Encode this equation as two pasting expressions of exact functors. Exact derived
   transformation pasting preserves their equality. Identify the invertible cells with
   the specified derived compositors, and the counit cells with the localized counits.
   This gives the first equation on every unbounded derived object.
4. Expand conjugation and substitute the counit equation. Naturality of the composite
   unit and its right triangle identity give the stated conjugate equality.
-/
theorem etaleSumCompositionCounit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v] :
    (∀ K : DerivedCategoryModule A T,
      (derivedEtaleSumCompIso A e v).hom.app
          ((upperStar (ModuleCat.{u + 1} A) (e ≫ v)).mapDerivedCategory.obj K) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (e ≫ v)
          inferInstance).counit.app K =
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
          (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory).map
            ((unboundedEtaleUpperStarCompIso A e v).hom.app K) ≫
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
          ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
            inferInstance).counit.app
              ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj K)) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
          inferInstance).counit.app K) ∧
    conjugateEquiv
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (e ≫ v)
          inferInstance)
        ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
            inferInstance).comp
          (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
            inferInstance))
        (derivedEtaleSumCompIso A e v).hom =
      (unboundedEtaleUpperStarCompIso A e v).hom := by
  let C : Fin 3 → Type (u + 2) := fun i ↦
    Sheaf ((![U, X, T]) i).smallEtaleTopology (ModuleCat.{u + 1} A)
  let le : Word C 0 1 := .edge (ExactFunctor.of
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance))
  let lv : Word C 1 2 := .edge (ExactFunctor.of
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance))
  let lev : Word C 0 2 := .edge (ExactFunctor.of
    (etaleLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) inferInstance))
  let re : Word C 1 0 := .edge (ExactFunctor.of (upperStar (ModuleCat.{u + 1} A) e))
  let rv : Word C 2 1 := .edge (ExactFunctor.of (upperStar (ModuleCat.{u + 1} A) v))
  let rev : Word C 2 0 := .edge (ExactFunctor.of
    (upperStar (ModuleCat.{u + 1} A) (e ≫ v)))
  let sigma : Expression C (.comp le lv) lev := .cell (etaleSumSheafCompIso A e v).hom
  let kappa : Expression C rev (.comp rv re) :=
    .cell (upperStarComp (ModuleCat.{u + 1} A) e v).hom
  let ee : Expression C (.comp re le) (.nil 1) := .cell
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).counit
  let ev : Expression C (.comp rv lv) (.nil 2) := .cell
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).counit
  let eev : Expression C (.comp rev lev) (.nil 2) := .cell
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (e ≫ v)
      inferInstance).counit
  let lhs : Expression C (.comp rev (.comp le lv)) (.nil 2) :=
    .vcomp (.input rev sigma) eev
  let rhs : Expression C (.comp rev (.comp le lv)) (.nil 2) :=
    .vcomp (.output kappa (.comp le lv))
      (.vcomp (.assoc rv re (.comp le lv))
        (.vcomp (.input rv (.vcomp (.assocInv re le lv)
          (.vcomp (.output ee lv) (.leftUnit lv)))) ev))
  have ho : lhs.ordinary = rhs.ordinary := by
    apply NatTrans.ext
    funext N
    simpa [lhs, rhs, sigma, kappa, ee, ev, eev, Expression.ordinary,
      le, lv, lev, re, rv, rev, Word.ordinary, C] using
      sheaf_composition_counit A e v N
  have hd := (exact_derived_transformation_pasting C).2.1 lhs rhs ho
  have hs : sigma.derived = (derivedEtaleSumCompIso A e v).hom := by
    change Word.cell C (P := .comp le lv) (R := lev) (etaleSumSheafCompIso A e v).hom = _
    rw [cell_iso]
    simp [le, lv, lev, Word.comparison, Word.ordinary, derivedEtaleSumCompIso]
  have hk : kappa.derived = (unboundedEtaleUpperStarCompIso A e v).hom := by
    change Word.cell C (P := rev) (R := .comp rv re)
      (upperStarComp (ModuleCat.{u + 1} A) e v).hom = _
    rw [cell_iso]
    simp only [re, rv, rev, Word.comparison, Word.ordinary, unboundedEtaleUpperStarCompIso,
      Iso.refl_inv, Iso.trans_hom,
      Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl, Iso.trans_refl]
    erw [Category.id_comp]
    rfl
  have he : ee.derived =
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
        inferInstance).counit := by
    exact cell_counit C (i := 0) (j := 1)
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance)
      (upperStar (ModuleCat.{u + 1} A) e)
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
  have hv : ev.derived =
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
        inferInstance).counit := by
    exact cell_counit C (i := 1) (j := 2)
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance)
      (upperStar (ModuleCat.{u + 1} A) v)
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
  have hev : eev.derived =
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (e ≫ v)
        inferInstance).counit := by
    exact cell_counit C (i := 0) (j := 2)
      (etaleLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) inferInstance)
      (upperStar (ModuleCat.{u + 1} A) (e ≫ v))
      (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (e ≫ v) inferInstance)
  have hder (K : DerivedCategoryModule A T) := congr_app hd K
  simp only [lhs, rhs, Expression.derived, hs, hk, he, hv, hev, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.assoc] at hder
  dsimp only [le, lv, re, rv, rev, Word.derived, Word.ordinary, ExactFunctor.of] at hder
  dsimp only [Functor.comp_obj, Functor.comp_map] at hder
  have hc (K : DerivedCategoryModule A T) :
      (derivedEtaleSumCompIso A e v).hom.app
          ((upperStar (ModuleCat.{u + 1} A) (e ≫ v)).mapDerivedCategory.obj K) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (e ≫ v)
          inferInstance).counit.app K =
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
          (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory).map
            ((unboundedEtaleUpperStarCompIso A e v).hom.app K) ≫
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
          ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
            inferInstance).counit.app
              ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj K)) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
          inferInstance).counit.app K := by
    let L := (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory
    let M := (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
    let R := (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory
    have h := hder K
    change _ = L.map (M.map ((unboundedEtaleUpperStarCompIso A e v).hom.app K)) ≫
      𝟙 (L.obj (M.obj ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj
        (R.obj K)))) ≫
      𝟙 (L.obj (M.obj ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj
        (R.obj K)))) ≫
      L.map ((derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
        inferInstance).counit.app (R.obj K)) ≫ 𝟙 (L.obj (R.obj K)) ≫
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
        inferInstance).counit.app K at h
    erw [Category.id_comp, Category.id_comp, Category.id_comp] at h
    exact h
  refine ⟨hc, ?_⟩
  apply conjugate_of_counit
  intro K
  simpa only [Adjunction.comp_counit_app, Category.assoc] using hc K

end AlgebraicGeometry.Etale
