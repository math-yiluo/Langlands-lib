/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation

/-! # Exact derived sum base change as an actual mate

Source: Stacks Project, Tag 03S6; exact localization of the sum-adjunction calculation.
(blueprint: lem-pur-etale-exact-sum-base-change-mate).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactDerivedPasting
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek
  Functor.mapDerivedCategory derivedEtaleLowerShriekUpperStarAdjunction
  unboundedEtaleUpperStarIdIso

private lemma mates_paste
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {L₀ : C₀ ⥤ D₀} {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
    {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {V₀₁ : C₀ ⥤ C₁} {V₁₂ : C₁ ⥤ C₂} {V₀₂ : C₀ ⥤ C₂}
    {W₀₁ : D₀ ⥤ D₁} {W₁₂ : D₁ ⥤ D₂} {W₀₂ : D₀ ⥤ D₂}
    (s : V₀₂ ≅ V₀₁ ⋙ V₁₂) (t : W₀₂ ≅ W₀₁ ⋙ W₁₂)
    (α : TwoSquare V₀₁ L₀ L₁ W₀₁) (β : TwoSquare V₁₂ L₁ L₂ W₁₂)
    (γ : TwoSquare V₀₂ L₀ L₂ W₀₂)
    (h : ∀ M, L₂.map (s.inv.app M) ≫ γ.app M ≫ t.hom.app (L₀.obj M) =
      β.app (V₀₁.obj M) ≫ W₁₂.map (α.app M)) (K : D₀) :
    V₁₂.map ((mateEquiv a₀ a₁ α).app K) ≫
        (mateEquiv a₁ a₂ β).app (W₀₁.obj K) =
      s.inv.app (R₀.obj K) ≫ (mateEquiv a₀ a₂ γ).app K ≫
        R₂.map (t.hom.app K) := by
  have hα := mateEquiv_counit a₀ a₁ α K
  change L₁.map ((mateEquiv a₀ a₁ α).app K) ≫ a₁.counit.app _ =
    α.app (R₀.obj K) ≫ W₀₁.map (a₀.counit.app K) at hα
  have hβ := mateEquiv_counit a₁ a₂ β (W₀₁.obj K)
  change L₂.map ((mateEquiv a₁ a₂ β).app _) ≫ a₂.counit.app _ =
    β.app (R₁.obj (W₀₁.obj K)) ≫ W₁₂.map (a₁.counit.app _) at hβ
  have hγ := mateEquiv_counit a₀ a₂ γ K
  change L₂.map ((mateEquiv a₀ a₂ γ).app K) ≫ a₂.counit.app _ =
    γ.app (R₀.obj K) ≫ W₀₂.map (a₀.counit.app K) at hγ
  have hn := β.naturality ((mateEquiv a₀ a₁ α).app K)
  change L₂.map (V₁₂.map ((mateEquiv a₀ a₁ α).app K)) ≫
    β.app (R₁.obj (W₀₁.obj K)) =
      β.app (V₀₁.obj (R₀.obj K)) ≫
        W₁₂.map (L₁.map ((mateEquiv a₀ a₁ α).app K)) at hn
  have ht := a₂.counit.naturality (t.hom.app K)
  change L₂.map (R₂.map (t.hom.app K)) ≫ a₂.counit.app (W₁₂.obj (W₀₁.obj K)) =
    a₂.counit.app (W₀₂.obj K) ≫ t.hom.app K at ht
  have he := t.hom.naturality (a₀.counit.app K)
  change W₀₂.map (a₀.counit.app K) ≫ t.hom.app K =
    t.hom.app (L₀.obj (R₀.obj K)) ≫ W₁₂.map (W₀₁.map (a₀.counit.app K)) at he
  apply (a₂.homEquiv _ _).symm.injective
  change L₂.map (_ ≫ _) ≫ a₂.counit.app _ =
    L₂.map (_ ≫ _ ≫ _) ≫ a₂.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  rw [hβ, ← Category.assoc, hn, Category.assoc, ← W₁₂.map_comp, hα,
    W₁₂.map_comp, ht, ← Category.assoc _ _ (t.hom.app K), hγ]
  simp only [Category.assoc]
  rw [he]
  simpa only [Category.assoc] using
    (h (R₀.obj K)).symm =≫ W₁₂.map (W₀₁.map (a₀.counit.app K))

private lemma mate_eq_of_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {V : C ⥤ E} {W : D ⥤ F}
    (α : TwoSquare V L L' W) (β : TwoSquare R W V R')
    (h : ∀ M, b.unit.app (V.obj M) ≫ R'.map (α.app M) =
      V.map (a.unit.app M) ≫ β.app (L.obj M)) :
    mateEquiv a b α = β := by
  apply (mateEquiv a b).symm.injective
  rw [Equiv.symm_apply_apply]
  ext M
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  exact (h M).trans (unit_mateEquiv_symm a b β M)

private lemma exact_word_cell_iso
    {I : Type*} (C : I → Type*) [∀ i, Category (C i)] [∀ i, Abelian (C i)]
    [∀ i, HasDerivedCategory (C i)] {i j : I}
    {P R : Word C i j}
    (alpha : P.ordinary.obj ≅ R.ordinary.obj) :
    Word.cell C alpha.hom = P.comparison.inv ≫
      (Functor.mapDerivedCategoryNatIso alpha).hom ≫ R.comparison.hom := rfl

private lemma exact_cell_counit
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

/-- Exact sum base change is the mate of the inverse exact pullback-square comparison.
Source: Stacks Project, Tag 03S6; the ordinary sum base-change unit equation and its exact
localization. (blueprint: lem-pur-etale-exact-sum-base-change-mate).

Proof: The ordinary sum base-change unit equation identifies its mate with the inverse
ordinary pullback-square comparison. Transpose it to a counit equation. Express both
sides as finite pastings of the exact inverse-image and sum functors, their square and
base-change cells, and their two counits. Exact-derived transformation pasting descends
the equality. The comparison cells descend to the specified exact square and sum
base-change isomorphisms. Localization of the complex adjunction identifies the counit
cells with the specified derived sum counits. Injectivity of the second adjunction's
hom-bijection gives the asserted equality on every unbounded object. -/
theorem etaleExactSumBaseChangeMate
    (A : Type (u + 1)) [CommRing A]
    {U U' X X' : Scheme.{u}} {e : U ⟶ X} {e' : U' ⟶ X'}
    {w : X' ⟶ X} {w' : U' ⟶ U} [Etale e] [Etale e']
    (sq : IsPullback w' e' e w) :
    (mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e' inferInstance)
      (TwoSquare.mk _ _ _ _
        (mapDerivedCategoryEtaleLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq).hom)
      ) =
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv := by
  let B := ModuleCat.{u + 1} A
  let a := etaleLowerShriekUpperStarAdjunction B e inferInstance
  let b := etaleLowerShriekUpperStarAdjunction B e' inferInstance
  let α := @asIso _ _ _ _ _ (isIso_etaleLowerShriekSquareBaseChangeMap B sq)
  let χ := (squareUpperStarIso B sq.toCommSq).symm
  have hs : mateEquiv a b (TwoSquare.mk _ _ _ _ α.hom) =
      TwoSquare.mk _ _ _ _ χ.hom := by
    apply mate_eq_of_unit
    intro M
    exact unit_map_etaleLowerShriekSquareBaseChangeMap_app B sq.toCommSq M
  let C : Fin 4 → Type (u + 2) := fun i ↦
    Sheaf (![U, X, U', X'] i).smallEtaleTopology B
  let l : Word C 0 1 := .edge (ExactFunctor.of (etaleLowerShriek B e inferInstance))
  let r : Word C 1 0 := .edge (ExactFunctor.of (upperStar B e))
  let l' : Word C 2 3 := .edge (ExactFunctor.of (etaleLowerShriek B e' inferInstance))
  let r' : Word C 3 2 := .edge (ExactFunctor.of (upperStar B e'))
  let v : Word C 0 2 := .edge (ExactFunctor.of (upperStar B w'))
  let z : Word C 1 3 := .edge (ExactFunctor.of (upperStar B w))
  let lhs : Expression C (.comp (.comp r v) l') z :=
    .vcomp (.output (.cell χ.hom : Expression C (.comp r v) (.comp z r')) l')
      (.vcomp (.assoc z r' l')
        (.vcomp (.input z (.cell b.counit : Expression C (.comp r' l') (.nil 3)))
          (.rightUnit z)))
  let rhs : Expression C (.comp (.comp r v) l') z :=
    .vcomp (.assoc r v l')
      (.vcomp (.input r (.cell α.hom : Expression C (.comp v l') (.comp l z)))
        (.vcomp (.assocInv r l z)
          (.vcomp (.output (.cell a.counit : Expression C (.comp r l) (.nil 1)) z)
            (.leftUnit z))))
  have ho : lhs.ordinary = rhs.ordinary := by
    apply NatTrans.ext
    funext N
    have hn := mateEquiv_counit a b (TwoSquare.mk _ _ _ _ α.hom) N
    rw [hs] at hn
    simpa only [lhs, rhs, Expression.ordinary, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
      Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id,
      TwoSquare.mk,
      l, r, l', r', v, z, Word.ordinary, ExactFunctor.of_fst] using hn
  have hd := (exact_derived_transformation_pasting C).2.1 lhs rhs ho
  have hα : Word.cell C (P := .comp v l') (R := .comp l z) α.hom =
      (mapDerivedCategoryEtaleLowerShriekBaseChangeIso B sq).hom := by
    rw [exact_word_cell_iso C (P := .comp v l') (R := .comp l z) α]
    simp only [v, l', l, z, Word.comparison,
      Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl, Iso.trans_refl]
    rfl
  have hχ : Word.cell C (P := .comp r v) (R := .comp z r') χ.hom =
      (exactDerivedSquareUpperStarIso B sq.toCommSq).inv := by
    rw [exact_word_cell_iso C (P := .comp r v) (R := .comp z r') χ]
    simp only [r, v, z, r', Word.comparison,
      Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl, Iso.trans_refl]
    simp only [χ, Functor.mapDerivedCategoryNatIso_symm,
      exactDerivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]
    rfl
  have ha : Word.cell C (P := .comp r l) (R := .nil 1) a.counit =
      (derivedEtaleLowerShriekUpperStarAdjunction B e inferInstance).counit := by
    simpa only [C, a, l, r, derivedEtaleLowerShriekUpperStarAdjunction,
      Adjunction.onDerivedCategory, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.succ_eq_add_one, Nat.reduceAdd]
      using exact_cell_counit C (i := 0) (j := 1) _ _ a
  have hb : Word.cell C (P := .comp r' l') (R := .nil 3) b.counit =
      (derivedEtaleLowerShriekUpperStarAdjunction B e' inferInstance).counit := by
    simpa only [C, b, l', r', derivedEtaleLowerShriekUpperStarAdjunction,
      Adjunction.onDerivedCategory, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.succ_eq_add_one, Nat.reduceAdd]
      using exact_cell_counit C (i := 2) (j := 3) _ _ b
  ext K
  have hK := NatTrans.congr_app hd K
  simp only [lhs, rhs, Expression.derived, hα, hχ, ha, hb,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Category.id_comp,
    l, r, l', r', v, z, Word.derived, Word.ordinary, ExactFunctor.of_fst] at hK
  simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id] at hK
  let adj' := derivedEtaleLowerShriekUpperStarAdjunction B e' inferInstance
  apply (adj'.homEquiv _ _).symm.injective
  change (etaleLowerShriek B e' inferInstance).mapDerivedCategory.map _ ≫
      (derivedEtaleLowerShriekUpperStarAdjunction B e' inferInstance).counit.app _ = _
  have hm := mateEquiv_counit
    (derivedEtaleLowerShriekUpperStarAdjunction B e inferInstance)
    (derivedEtaleLowerShriekUpperStarAdjunction B e' inferInstance)
    (TwoSquare.mk _ _ _ _ (mapDerivedCategoryEtaleLowerShriekBaseChangeIso B sq).hom) K
  exact hm.trans hK.symm

private lemma conjugate_horizontal
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ L₁' : C ⥤ D} {R₁ R₁' : D ⥤ C}
    {L₂ L₂' : D ⥤ E} {R₂ R₂' : E ⥤ D}
    (a₁ : L₁ ⊣ R₁) (b₁ : L₁' ⊣ R₁')
    (a₂ : L₂ ⊣ R₂) (b₂ : L₂' ⊣ R₂')
    (x : L₁' ⟶ L₁) (y : L₂' ⟶ L₂) :
    conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) (NatTrans.hcomp x y) =
      Functor.whiskerLeft R₂ (conjugateEquiv a₁ b₁ x) ≫
        Functor.whiskerRight (conjugateEquiv a₂ b₂ y) R₁' := by
  rw [Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight]
  rw [← conjugateEquiv_comp (a₁.comp a₂) (b₁.comp a₂) (b₁.comp b₂),
    conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft]

private lemma conjugate_compositor_refinement
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ L₁' : C ⥤ D} {R₁ R₁' : D ⥤ C}
    {L₂ L₂' : D ⥤ E} {R₂ R₂' : E ⥤ D}
    {L₃ L₃' : C ⥤ E} {R₃ R₃' : E ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (b₁ : L₁' ⊣ R₁') (b₂ : L₂' ⊣ R₂') (b₃ : L₃' ⊣ R₃')
    (t : L₁ ≅ L₁') (u : L₂ ≅ L₂') (v : L₃ ≅ L₃')
    (α : L₁ ⋙ L₂ ≅ L₃) (β : L₁' ⋙ L₂' ≅ L₃')
    (h : α.hom ≫ v.hom = NatTrans.hcomp t.hom u.hom ≫ β.hom) (K : E) :
    (conjugateIsoEquiv b₃ a₃ v).hom.app K ≫
        (conjugateIsoEquiv a₃ (a₁.comp a₂) α).hom.app K =
      (conjugateIsoEquiv b₃ (b₁.comp b₂) β).hom.app K ≫
        (conjugateIsoEquiv b₁ a₁ t).hom.app (R₂'.obj K) ≫
        R₁.map ((conjugateIsoEquiv b₂ a₂ u).hom.app K) := by
  have hc := congrArg (conjugateEquiv b₃ (a₁.comp a₂)) h
  rw [← conjugateEquiv_comp b₃ a₃ (a₁.comp a₂),
    ← conjugateEquiv_comp b₃ (b₁.comp b₂) (a₁.comp a₂),
    conjugate_horizontal] at hc
  simpa only [conjugateIsoEquiv_apply_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    using NatTrans.congr_app hc K

/-- Pasting naturality squares through two specified compositor isomorphisms. -/
private theorem normalization_pasting
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {G₀ P₀ : C₀ ⥤ D₀} {G₁ P₁ : C₁ ⥤ D₁} {G₂ P₂ : C₂ ⥤ D₂}
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
    {H₀₁ : D₀ ⥤ D₁} {H₁₂ : D₁ ⥤ D₂} {H₀₂ : D₀ ⥤ D₂}
    (s : H₀₂ ≅ H₀₁ ⋙ H₁₂) (t : F₀₂ ≅ F₀₁ ⋙ F₁₂)
    (r₀ : G₀ ⟶ P₀) (r₁ : G₁ ⟶ P₁) (r₂ : G₂ ⟶ P₂)
    (b₀₁ : G₀ ⋙ H₀₁ ⟶ F₀₁ ⋙ G₁) (b₁₂ : G₁ ⋙ H₁₂ ⟶ F₁₂ ⋙ G₂)
    (b₀₂ : G₀ ⋙ H₀₂ ⟶ F₀₂ ⋙ G₂)
    (q₀₁ : P₀ ⋙ H₀₁ ⟶ F₀₁ ⋙ P₁) (q₁₂ : P₁ ⋙ H₁₂ ⟶ F₁₂ ⋙ P₂)
    (q₀₂ : P₀ ⋙ H₀₂ ⟶ F₀₂ ⋙ P₂) (K : C₀)
    (hb : H₁₂.map (b₀₁.app K) ≫ b₁₂.app (F₀₁.obj K) =
      s.inv.app (G₀.obj K) ≫ b₀₂.app K ≫ G₂.map (t.hom.app K))
    (hq : H₁₂.map (q₀₁.app K) ≫ q₁₂.app (F₀₁.obj K) =
      s.inv.app (P₀.obj K) ≫ q₀₂.app K ≫ P₂.map (t.hom.app K))
    (h₀₁ : b₀₁.app K ≫ r₁.app (F₀₁.obj K) =
      H₀₁.map (r₀.app K) ≫ q₀₁.app K)
    (h₁₂ : b₁₂.app (F₀₁.obj K) ≫ r₂.app (F₁₂.obj (F₀₁.obj K)) =
      H₁₂.map (r₁.app (F₀₁.obj K)) ≫ q₁₂.app (F₀₁.obj K)) :
    b₀₂.app K ≫ r₂.app (F₀₂.obj K) = H₀₂.map (r₀.app K) ≫ q₀₂.app K := by
  apply (cancel_epi (s.inv.app (G₀.obj K))).1
  apply (cancel_mono (P₂.map (t.hom.app K))).1
  have hn := r₂.naturality (t.hom.app K)
  have hs := s.inv.naturality (r₀.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hs
  simp only [Category.assoc]
  rw [← hn, ← Category.assoc (b₀₂.app K), ← Category.assoc (s.inv.app _), ← hb]
  rw [Category.assoc, h₁₂, ← Category.assoc, ← H₁₂.map_comp, h₀₁,
    H₁₂.map_comp, Category.assoc, hq]
  rw [← Category.assoc, ← Category.assoc, hs]
  simp only [Category.assoc]

private lemma derived_sum_identity
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    conjugateEquiv
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)
          inferInstance) Adjunction.id
        (Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)
              inferInstance) (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
          Functor.mapDerivedCategoryIdIso _).inv =
      (unboundedEtaleUpperStarIdIso A X).hom := by
  let B := ModuleCat.{u + 1} A
  let a := etaleLowerShriekUpperStarAdjunction B (𝟙 X) inferInstance
  let i := Adjunction.leftAdjointIdIso a (upperStarId B X)
  have hs : conjugateEquiv a Adjunction.id i.inv = (upperStarId B X).hom := by
    apply (cancel_epi (upperStarId B X).inv).1
    calc
      _ = conjugateEquiv Adjunction.id a i.hom ≫
          conjugateEquiv a Adjunction.id i.inv := by
        rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
      _ = 𝟙 _ := by
        rw [conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id]
      _ = _ := (upperStarId B X).inv_hom_id.symm
  let C : Fin 1 → Type (u + 2) := fun _ ↦ Sheaf X.smallEtaleTopology B
  let l : Word C 0 0 := .edge (ExactFunctor.of (etaleLowerShriek B (𝟙 X) inferInstance))
  let r : Word C 0 0 := .edge (ExactFunctor.of (upperStar B (𝟙 X)))
  let lhs : Expression C r (.nil 0) :=
    .vcomp (.rightUnitInv r) (.vcomp
      (.input r (.cell i.inv : Expression C (.nil 0) l))
      (.cell a.counit : Expression C (.comp r l) (.nil 0)))
  let rhs : Expression C r (.nil 0) := .cell (upperStarId B X).hom
  have ho : lhs.ordinary = rhs.ordinary := by
    apply NatTrans.ext
    funext M
    simpa only [lhs, rhs, Expression.ordinary, NatTrans.comp_app,
      Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Category.id_comp,
      conjugateEquiv_adjunction_id, r, Word.ordinary, ExactFunctor.of_fst]
      using NatTrans.congr_app hs M
  have hd := (exact_derived_transformation_pasting C).2.1 lhs rhs ho
  have hl : Word.cell C (P := .nil 0) (R := l) i.inv =
      (Functor.mapDerivedCategoryNatIso i ≪≫ Functor.mapDerivedCategoryIdIso _).inv := by
    rw [show i.inv = i.symm.hom from rfl, exact_word_cell_iso C (P := .nil 0) (R := l) i.symm]
    simp only [l, Word.comparison, Iso.refl_hom, Category.comp_id,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_inv]
    rfl
  have hr : Word.cell C (P := r) (R := .nil 0) (upperStarId B X).hom =
      (unboundedEtaleUpperStarIdIso A X).hom := by
    rw [exact_word_cell_iso C (P := r) (R := .nil 0) (upperStarId B X)]
    simp only [r, C, B, Word.comparison, Word.ordinary, ExactFunctor.of_fst,
      Iso.refl_inv, unboundedEtaleUpperStarIdIso, Iso.trans_hom]
    erw [Category.id_comp]
  have he : Word.cell C (P := .comp r l) (R := .nil 0) a.counit =
      (derivedEtaleLowerShriekUpperStarAdjunction B (𝟙 X) inferInstance).counit := by
    simpa only [derivedEtaleLowerShriekUpperStarAdjunction, Adjunction.onDerivedCategory]
      using exact_cell_counit C _ _ a
  apply NatTrans.ext
  funext K
  rw [conjugateEquiv_adjunction_id]
  have hK := NatTrans.congr_app hd K
  simpa only [lhs, rhs, Expression.derived, hl, hr, he, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Category.id_comp,
    r, Word.derived, Word.ordinary, ExactFunctor.of_fst] using hK

end AlgebraicGeometry.Etale
