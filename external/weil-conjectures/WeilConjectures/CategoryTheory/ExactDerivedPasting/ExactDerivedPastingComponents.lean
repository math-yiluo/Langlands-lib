/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import all WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows

/-! # Components for finite exact-derived pasting

Source: Stacks, Tags 015F and 04VG.
(blueprint: lem-cbc-exact-derived-pasting-components)

The public congruence theorem and the private component calculations let applications
use finite expression trees without unfolding sheaf inverse-image constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSimpArgs false
universe u t v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale.StrictTower
namespace CategoryTheory.ExactDerivedPasting

private theorem exactPairAdditive {A D : Type*} [Category A] [Category D]
    [Abelian A] [Abelian D] (F : A ⥤ₑ D) : F.obj.Additive :=
  exactFunctor_le_additiveFunctor A D F.obj F.property

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Generic
variable {I : Type t} (C : I → Type u) [∀ i, Category.{v} (C i)]
  [∀ i, Abelian (C i)] [∀ i, HasDerivedCategory.{w} (C i)]

private theorem genericCell_of_factors {X Y : I}
    (P R : Word (C) X Y) (a : P.ordinary.obj ⟶ R.ordinary.obj)
    (d : P.derived ⟶ R.derived)
    (hd : ∀ K : CochainComplex (C X) ℤ,
      d.app (DerivedCategory.Q.obj K) ≫ (wordFactors (C) R).hom.app K =
        (wordFactors (C) P).hom.app K ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K)) :
    Word.cell (C) a = d := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (C X) (.up ℤ))
  intro K
  apply (cancel_mono ((wordFactors (C) R).hom.app K)).mp
  exact (cell_factors (C) a K).trans (hd K).symm

omit [∀ i, HasDerivedCategory.{w} (C i)] in
private theorem exactEdgeAdditive {X Y : I} (F : C X ⥤ₑ C Y) : F.obj.Additive :=
  exactFunctor_le_additiveFunctor (C X) (C Y) F.obj F.property

attribute [local instance] exactEdgeAdditive

private theorem genericEdgeFactors {X Y : I}
    (F : C X ⥤ₑ C Y)
    (K : CochainComplex (C X) ℤ) :
    (wordFactors C (.edge F)).hom.app K =
      F.obj.mapDerivedCategoryFactors.hom.app K := by
  change (𝟙 _ ≫ F.obj.mapDerivedCategoryFactors.hom.app K) =
    F.obj.mapDerivedCategoryFactors.hom.app K
  exact Category.id_comp _

private theorem genericCompCell {X Y Z : I}
    (F : C X ⥤ₑ C Y) (H : C Y ⥤ₑ C Z) (L : C X ⥤ₑ C Z)
    (a : F.obj ⋙ H.obj ⟶ L.obj)
    (d : F.obj.mapDerivedCategory ⋙ H.obj.mapDerivedCategory ⟶
      L.obj.mapDerivedCategory)
    (hd : compCompatible F.obj H.obj L.obj a d) :
    Word.cell C (P := .comp (.edge F) (.edge H)) (R := .edge L) a = d := by
  apply genericCell_of_factors
  intro K
  simpa only [wordFactors_comp, genericEdgeFactors, Word.ordinary, Word.derived,
    Category.assoc] using hd K

private theorem genericSquareCell {X Y Z T : I}
    (F : C X ⥤ₑ C Y) (H : C Y ⥤ₑ C Z)
    (G : C X ⥤ₑ C T) (L : C T ⥤ₑ C Z)
    (a : F.obj ⋙ H.obj ⟶ G.obj ⋙ L.obj)
    (d : F.obj.mapDerivedCategory ⋙ H.obj.mapDerivedCategory ⟶
      G.obj.mapDerivedCategory ⋙ L.obj.mapDerivedCategory)
    (hd : squareCompatible F.obj H.obj G.obj L.obj a d) :
    Word.cell C (P := .comp (.edge F) (.edge H))
      (R := .comp (.edge G) (.edge L)) a = d := by
  apply genericCell_of_factors
  intro K
  simpa only [wordFactors_comp, genericEdgeFactors, Word.ordinary, Word.derived,
    Category.assoc] using hd K

private theorem genericSquareIsoSymm {X Y Z T : I}
    (F : C X ⥤ₑ C Y) (H : C Y ⥤ₑ C Z)
    (G : C X ⥤ₑ C T) (L : C T ⥤ₑ C Z) (e : F.obj ⋙ H.obj ≅ G.obj ⋙ L.obj) :
    (Functor.mapDerivedCategorySquareIso e).symm =
      Functor.mapDerivedCategorySquareIso e.symm := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Category.assoc]

/-- Ordinary equality of finite pasting expressions implies equality after exact localization.
Source: Stacks, Tags 015F and 04VG
(blueprint: lem-cbc-exact-derived-pasting-components).
Proof: Precompose both derived transformations with the localization functor Q.
The word-factorization equations identify their components with Q applied to the
ordinary complex components, followed by the same invertible target comparison.
The assumed ordinary equality identifies these components. Cancel the target
comparison and use the fully faithful natural-transformation restriction along Q.
Each expression is finite by construction; the indexing type need not be finite. -/
theorem exactPasting_congr {X Y : I}
    {P R : Word (C) X Y}
    (e f : Expression (C) P R) (h : e.ordinary = f.ordinary) :
    e.derived = f.derived := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (C X) (.up ℤ))
  intro K
  apply (cancel_mono ((wordFactors (C) R).hom.app K)).mp
  rw [expression_factors, expression_factors, h]

private theorem genericVerticalDerived {a c e b d f : I}
    (K : C a ⥤ₑ C b) (L : C c ⥤ₑ C d) (J : C e ⥤ₑ C f)
    (R₁ : C c ⥤ₑ C a) (R₂ : C e ⥤ₑ C c) (R : C e ⥤ₑ C a)
    (P₁ : C d ⥤ₑ C b) (P₂ : C f ⥤ₑ C d) (P : C f ⥤ₑ C b)
    (a₁ : L.obj ⋙ P₁.obj ⟶ R₁.obj ⋙ K.obj)
    (a₂ : J.obj ⋙ P₂.obj ⟶ R₂.obj ⋙ L.obj)
    (ao : J.obj ⋙ P.obj ⟶ R.obj ⋙ K.obj)
    (cp : P.obj ⟶ P₂.obj ⋙ P₁.obj) (cr : R.obj ⟶ R₂.obj ⋙ R₁.obj)
    (d₁ : L.obj.mapDerivedCategory ⋙ P₁.obj.mapDerivedCategory ⟶
      R₁.obj.mapDerivedCategory ⋙ K.obj.mapDerivedCategory)
    (d₂ : J.obj.mapDerivedCategory ⋙ P₂.obj.mapDerivedCategory ⟶
      R₂.obj.mapDerivedCategory ⋙ L.obj.mapDerivedCategory)
    (d₀ : J.obj.mapDerivedCategory ⋙ P.obj.mapDerivedCategory ⟶
      R.obj.mapDerivedCategory ⋙ K.obj.mapDerivedCategory)
    (dp : P.obj.mapDerivedCategory ⟶ P₂.obj.mapDerivedCategory ⋙ P₁.obj.mapDerivedCategory)
    (dr : R.obj.mapDerivedCategory ⟶ R₂.obj.mapDerivedCategory ⋙ R₁.obj.mapDerivedCategory)
    (h₁ : Word.cell C (P := .comp (.edge L) (.edge P₁))
      (R := .comp (.edge R₁) (.edge K)) a₁ = d₁)
    (h₂ : Word.cell C (P := .comp (.edge J) (.edge P₂))
      (R := .comp (.edge R₂) (.edge L)) a₂ = d₂)
    (h₀ : Word.cell C (P := .comp (.edge J) (.edge P))
      (R := .comp (.edge R) (.edge K)) ao = d₀)
    (hp : Word.cell C (P := .edge P) (R := .comp (.edge P₂) (.edge P₁)) cp = dp)
    (hr : Word.cell C (P := .edge R) (R := .comp (.edge R₂) (.edge R₁)) cr = dr)
    (h : Functor.whiskerLeft J.obj cp ≫ (Functor.associator J.obj P₂.obj P₁.obj).inv ≫
        Functor.whiskerRight a₂ P₁.obj ≫ (Functor.associator R₂.obj L.obj P₁.obj).hom ≫
        Functor.whiskerLeft R₂.obj a₁ ≫ (Functor.associator R₂.obj R₁.obj K.obj).inv =
      ao ≫ Functor.whiskerRight cr K.obj) :
    ∀ N : DerivedCategory (C e),
      dp.app (J.obj.mapDerivedCategory.obj N) ≫ P₁.obj.mapDerivedCategory.map (d₂.app N) ≫
          d₁.app (R₂.obj.mapDerivedCategory.obj N) =
        d₀.app N ≫ K.obj.mapDerivedCategory.map (dr.app N) := by
  let e₁ : Expression C (.comp (.edge L) (.edge P₁))
      (.comp (.edge R₁) (.edge K)) := .cell a₁
  let e₂ : Expression C (.comp (.edge J) (.edge P₂))
      (.comp (.edge R₂) (.edge L)) := .cell a₂
  let e₀ : Expression C (.comp (.edge J) (.edge P))
      (.comp (.edge R) (.edge K)) := .cell ao
  let ep : Expression C (.edge P) (.comp (.edge P₂) (.edge P₁)) := .cell cp
  let er : Expression C (.edge R) (.comp (.edge R₂) (.edge R₁)) := .cell cr
  let lhs := (Expression.input (.edge J) ep).vcomp
    ((Expression.assocInv (.edge J) (.edge P₂) (.edge P₁)).vcomp
    ((e₂.output (.edge P₁)).vcomp
    ((Expression.assoc (.edge R₂) (.edge L) (.edge P₁)).vcomp
    ((Expression.input (.edge R₂) e₁).vcomp
      (Expression.assocInv (.edge R₂) (.edge R₁) (.edge K))))))
  let rhs := e₀.vcomp (er.output (.edge K))
  have he : lhs.ordinary = rhs.ordinary := by
    simpa only [lhs, rhs, e₁, e₂, e₀, ep, er, Expression.ordinary, Word.ordinary] using h
  have hd := exactPasting_congr C lhs rhs he
  simp only [lhs, rhs, e₁, e₂, e₀, ep, er, Expression.derived, h₁, h₂, h₀, hp, hr] at hd
  intro N
  simpa only [Word.derived, Word.ordinary, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app hd N

private theorem genericHorizontalDerived {a c e b d f : I}
    (K : C a ⥤ₑ C b) (L : C b ⥤ₑ C e) (KL : C a ⥤ₑ C e)
    (V : C c ⥤ₑ C d) (J : C d ⥤ₑ C f) (VJ : C c ⥤ₑ C f)
    (R : C c ⥤ₑ C a) (P : C d ⥤ₑ C b) (Q : C f ⥤ₑ C e)
    (a₁ : V.obj ⋙ P.obj ⟶ R.obj ⋙ K.obj)
    (a₂ : J.obj ⋙ Q.obj ⟶ P.obj ⋙ L.obj)
    (ao : VJ.obj ⋙ Q.obj ⟶ R.obj ⋙ KL.obj)
    (ci : V.obj ⋙ J.obj ⟶ VJ.obj) (ck : K.obj ⋙ L.obj ⟶ KL.obj)
    (d₁ : V.obj.mapDerivedCategory ⋙ P.obj.mapDerivedCategory ⟶
      R.obj.mapDerivedCategory ⋙ K.obj.mapDerivedCategory)
    (d₂ : J.obj.mapDerivedCategory ⋙ Q.obj.mapDerivedCategory ⟶
      P.obj.mapDerivedCategory ⋙ L.obj.mapDerivedCategory)
    (d₀ : VJ.obj.mapDerivedCategory ⋙ Q.obj.mapDerivedCategory ⟶
      R.obj.mapDerivedCategory ⋙ KL.obj.mapDerivedCategory)
    (di : V.obj.mapDerivedCategory ⋙ J.obj.mapDerivedCategory ⟶ VJ.obj.mapDerivedCategory)
    (dk : K.obj.mapDerivedCategory ⋙ L.obj.mapDerivedCategory ⟶ KL.obj.mapDerivedCategory)
    (h₁ : Word.cell C (P := .comp (.edge V) (.edge P))
      (R := .comp (.edge R) (.edge K)) a₁ = d₁)
    (h₂ : Word.cell C (P := .comp (.edge J) (.edge Q))
      (R := .comp (.edge P) (.edge L)) a₂ = d₂)
    (h₀ : Word.cell C (P := .comp (.edge VJ) (.edge Q))
      (R := .comp (.edge R) (.edge KL)) ao = d₀)
    (hi : Word.cell C (P := .comp (.edge V) (.edge J)) (R := .edge VJ) ci = di)
    (hk : Word.cell C (P := .comp (.edge K) (.edge L)) (R := .edge KL) ck = dk)
    (h : Functor.whiskerRight ci Q.obj ≫ ao =
      (Functor.associator V.obj J.obj Q.obj).hom ≫ Functor.whiskerLeft V.obj a₂ ≫
        (Functor.associator V.obj P.obj L.obj).inv ≫ Functor.whiskerRight a₁ L.obj ≫
        (Functor.associator R.obj K.obj L.obj).hom ≫ Functor.whiskerLeft R.obj ck) :
    ∀ N : DerivedCategory (C c),
      Q.obj.mapDerivedCategory.map (di.app N) ≫ d₀.app N =
        d₂.app (V.obj.mapDerivedCategory.obj N) ≫ L.obj.mapDerivedCategory.map (d₁.app N) ≫
          dk.app (R.obj.mapDerivedCategory.obj N) := by
  let e₁ : Expression C (.comp (.edge V) (.edge P))
      (.comp (.edge R) (.edge K)) := .cell a₁
  let e₂ : Expression C (.comp (.edge J) (.edge Q))
      (.comp (.edge P) (.edge L)) := .cell a₂
  let e₀ : Expression C (.comp (.edge VJ) (.edge Q))
      (.comp (.edge R) (.edge KL)) := .cell ao
  let ei : Expression C (.comp (.edge V) (.edge J)) (.edge VJ) := .cell ci
  let ek : Expression C (.comp (.edge K) (.edge L)) (.edge KL) := .cell ck
  let lhs := (ei.output (.edge Q)).vcomp e₀
  let rhs := (Expression.assoc (.edge V) (.edge J) (.edge Q)).vcomp
    ((Expression.input (.edge V) e₂).vcomp
    ((Expression.assocInv (.edge V) (.edge P) (.edge L)).vcomp
    ((e₁.output (.edge L)).vcomp
    ((Expression.assoc (.edge R) (.edge K) (.edge L)).vcomp
      (Expression.input (.edge R) ek)))))
  have he : lhs.ordinary = rhs.ordinary := by
    simpa only [lhs, rhs, e₁, e₂, e₀, ei, ek, Expression.ordinary, Word.ordinary] using h
  have hd := exactPasting_congr C lhs rhs he
  simp only [lhs, rhs, e₁, e₂, e₀, ei, ek, Expression.derived, h₁, h₂, h₀, hi, hk] at hd
  intro N
  simpa only [Word.derived, Word.ordinary, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app hd N

private theorem genericCubeDerived {v s w t v₁ s₁ w₁ t₁ : I}
    (K : C v ⥤ₑ C w) (V : C s ⥤ₑ C t) (R : C s ⥤ₑ C v) (P : C t ⥤ₑ C w)
    (K₁ : C v₁ ⥤ₑ C w₁) (V₁ : C s₁ ⥤ₑ C t₁)
    (R₁ : C s₁ ⥤ₑ C v₁) (P₁ : C t₁ ⥤ₑ C w₁)
    (A : C w ⥤ₑ C w₁) (B' : C t ⥤ₑ C t₁)
    (C' : C s ⥤ₑ C s₁) (D : C v ⥤ₑ C v₁)
    (ao : V.obj ⋙ P.obj ⟶ R.obj ⋙ K.obj)
    (a₁ : V₁.obj ⋙ P₁.obj ⟶ R₁.obj ⋙ K₁.obj)
    (bk : K.obj ⋙ A.obj ⟶ D.obj ⋙ K₁.obj)
    (bi : V.obj ⋙ B'.obj ⟶ C'.obj ⋙ V₁.obj)
    (sp : B'.obj ⋙ P₁.obj ⟶ P.obj ⋙ A.obj)
    (sr : R.obj ⋙ D.obj ⟶ C'.obj ⋙ R₁.obj)
    (d₀ : V.obj.mapDerivedCategory ⋙ P.obj.mapDerivedCategory ⟶
      R.obj.mapDerivedCategory ⋙ K.obj.mapDerivedCategory)
    (d₁ : V₁.obj.mapDerivedCategory ⋙ P₁.obj.mapDerivedCategory ⟶
      R₁.obj.mapDerivedCategory ⋙ K₁.obj.mapDerivedCategory)
    (dbk : K.obj.mapDerivedCategory ⋙ A.obj.mapDerivedCategory ⟶
      D.obj.mapDerivedCategory ⋙ K₁.obj.mapDerivedCategory)
    (dbi : V.obj.mapDerivedCategory ⋙ B'.obj.mapDerivedCategory ⟶
      C'.obj.mapDerivedCategory ⋙ V₁.obj.mapDerivedCategory)
    (dp : B'.obj.mapDerivedCategory ⋙ P₁.obj.mapDerivedCategory ⟶
      P.obj.mapDerivedCategory ⋙ A.obj.mapDerivedCategory)
    (dr : R.obj.mapDerivedCategory ⋙ D.obj.mapDerivedCategory ⟶
      C'.obj.mapDerivedCategory ⋙ R₁.obj.mapDerivedCategory)
    (h₀ : Word.cell C (P := .comp (.edge V) (.edge P))
      (R := .comp (.edge R) (.edge K)) ao = d₀)
    (h₁ : Word.cell C (P := .comp (.edge V₁) (.edge P₁))
      (R := .comp (.edge R₁) (.edge K₁)) a₁ = d₁)
    (hk : Word.cell C (P := .comp (.edge K) (.edge A))
      (R := .comp (.edge D) (.edge K₁)) bk = dbk)
    (hi : Word.cell C (P := .comp (.edge V) (.edge B'))
      (R := .comp (.edge C') (.edge V₁)) bi = dbi)
    (hp : Word.cell C (P := .comp (.edge B') (.edge P₁))
      (R := .comp (.edge P) (.edge A)) sp = dp)
    (hr : Word.cell C (P := .comp (.edge R) (.edge D))
      (R := .comp (.edge C') (.edge R₁)) sr = dr)
    (h : Functor.whiskerLeft V.obj sp ≫ (Functor.associator V.obj P.obj A.obj).inv ≫
        Functor.whiskerRight ao A.obj ≫ (Functor.associator R.obj K.obj A.obj).hom ≫
        Functor.whiskerLeft R.obj bk ≫ (Functor.associator R.obj D.obj K₁.obj).inv ≫
        Functor.whiskerRight sr K₁.obj =
      (Functor.associator V.obj B'.obj P₁.obj).inv ≫ Functor.whiskerRight bi P₁.obj ≫
        (Functor.associator C'.obj V₁.obj P₁.obj).hom ≫ Functor.whiskerLeft C'.obj a₁ ≫
        (Functor.associator C'.obj R₁.obj K₁.obj).inv) :
    ∀ N : DerivedCategory (C s),
      dp.app (V.obj.mapDerivedCategory.obj N) ≫ A.obj.mapDerivedCategory.map (d₀.app N) ≫
          dbk.app (R.obj.mapDerivedCategory.obj N) ≫ K₁.obj.mapDerivedCategory.map (dr.app N) =
        P₁.obj.mapDerivedCategory.map (dbi.app N) ≫ d₁.app (C'.obj.mapDerivedCategory.obj N) := by
  let e₀ : Expression C (.comp (.edge V) (.edge P))
      (.comp (.edge R) (.edge K)) := .cell ao
  let e₁ : Expression C (.comp (.edge V₁) (.edge P₁))
      (.comp (.edge R₁) (.edge K₁)) := .cell a₁
  let ek : Expression C (.comp (.edge K) (.edge A))
      (.comp (.edge D) (.edge K₁)) := .cell bk
  let ei : Expression C (.comp (.edge V) (.edge B'))
      (.comp (.edge C') (.edge V₁)) := .cell bi
  let ep : Expression C (.comp (.edge B') (.edge P₁))
      (.comp (.edge P) (.edge A)) := .cell sp
  let er : Expression C (.comp (.edge R) (.edge D))
      (.comp (.edge C') (.edge R₁)) := .cell sr
  let lhs := (Expression.input (.edge V) ep).vcomp
    ((Expression.assocInv (.edge V) (.edge P) (.edge A)).vcomp
    ((e₀.output (.edge A)).vcomp
    ((Expression.assoc (.edge R) (.edge K) (.edge A)).vcomp
    ((Expression.input (.edge R) ek).vcomp
    ((Expression.assocInv (.edge R) (.edge D) (.edge K₁)).vcomp
      (er.output (.edge K₁)))))))
  let rhs := (Expression.assocInv (.edge V) (.edge B') (.edge P₁)).vcomp
    ((ei.output (.edge P₁)).vcomp
    ((Expression.assoc (.edge C') (.edge V₁) (.edge P₁)).vcomp
    ((Expression.input (.edge C') e₁).vcomp
      (Expression.assocInv (.edge C') (.edge R₁) (.edge K₁)))))
  have he : lhs.ordinary = rhs.ordinary := by
    simpa only [lhs, rhs, e₀, e₁, ek, ei, ep, er, Expression.ordinary, Word.ordinary] using h
  have hd := exactPasting_congr C lhs rhs he
  simp only [lhs, rhs, e₀, e₁, ek, ei, ep, er, Expression.derived, h₀, h₁, hk, hi, hp, hr] at hd
  intro N
  simpa only [Word.derived, Word.ordinary, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app hd N

end Generic

section TermwiseComponents
variable {A D E F : Type t} [Category.{v} A] [Category.{v} D]
  [Category.{v} E] [Category.{v} F]

private theorem termwiseComposite_app_app
    (f : A ⥤ D) (g : D ⥤ F) (h : A ⥤ E) (k : E ⥤ F)
    (τ : f ⋙ g ⟶ h ⋙ k) (M : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ) :
    ((Functor.termwiseCompositeTransformation ℕᵒᵖ A D E F f g h k τ).app M).app n =
      τ.app (M.obj n) := by
  simp only [Functor.termwiseCompositeTransformation, Functor.whiskeringRightObjCompIso,
    Functor.whiskeringRight, Functor.comp_obj, Iso.refl_hom, Iso.refl_inv,
    NatTrans.comp_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id]

private theorem termwiseToComp_app_app
    (f : A ⥤ D) (g : D ⥤ E) (h : A ⥤ E) (e : h ≅ f ⋙ g)
    (M : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ) :
    ((((Functor.whiskeringRight ℕᵒᵖ A E).mapIso e ≪≫
      Functor.whiskeringRightObjCompIso f g).hom.app M).app n) =
        e.hom.app (M.obj n) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.whiskeringRightObjCompIso,
    Functor.whiskeringRight, Functor.comp_obj, Iso.refl_hom, Iso.refl_inv,
    NatTrans.comp_app, NatTrans.id_app, Category.comp_id]

private theorem termwiseComp_app_app
    (f : A ⥤ D) (g : D ⥤ E) (h : A ⥤ E) (τ : f ⋙ g ⟶ h)
    (M : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ) :
    ((termwiseCompHom f g h τ).app M).app n = τ.app (M.obj n) := by
  simp only [termwiseCompHom, Functor.whiskeringRightObjCompIso,
    Functor.whiskeringRight, Functor.comp_obj, Iso.refl_hom, Iso.refl_inv,
    NatTrans.comp_app, NatTrans.id_app, Category.id_comp]

private theorem termwiseSquare_app_app
    (f : A ⥤ D) (g : D ⥤ F) (h : A ⥤ E) (k : E ⥤ F)
    (e : f ⋙ g ≅ h ⋙ k) (M : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ) :
    (((Functor.whiskeringRightObjCompIso f g ≪≫
      (Functor.whiskeringRight ℕᵒᵖ A F).mapIso e ≪≫
      (Functor.whiskeringRightObjCompIso h k).symm).hom.app M).app n) =
        e.hom.app (M.obj n) := by
  simpa only [towerSquare] using towerSquare_hom_app f g h k e M n

private theorem towerSquare_inv_app_app
    (f : A ⥤ D) (g : D ⥤ F) (h : A ⥤ E) (k : E ⥤ F)
    (e : f ⋙ g ≅ h ⋙ k) (M : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ) :
    ((towerSquare f g h k e).inv.app M).app n = e.inv.app (M.obj n) := by
  change ((towerSquare f g h k e).symm.hom.app M).app n = _
  rw [← towerSquare_symm]
  exact towerSquare_hom_app h k f g e.symm M n

end TermwiseComponents

section TowerLaws
variable {I : Type t} (C : I → Type u) [∀ i, Category.{v} (C i)]

private abbrev twFunctor {a b : I} (F : C a ⥤ C b) :=
  (Functor.whiskeringRight ℕᵒᵖ (C a) (C b)).obj F

private theorem verticalTowerLaw {a c e b d f : I}
    (K : C a ⥤ C b) (L : C c ⥤ C d) (J : C e ⥤ C f)
    (R₁ : C c ⥤ C a) (R₂ : C e ⥤ C c) (R : C e ⥤ C a)
    (P₁ : C d ⥤ C b) (P₂ : C f ⥤ C d) (P : C f ⥤ C b)
    (a₁ : L ⋙ P₁ ⟶ R₁ ⋙ K) (a₂ : J ⋙ P₂ ⟶ R₂ ⋙ L)
    (ao : J ⋙ P ⟶ R ⋙ K) (cp : P ≅ P₂ ⋙ P₁) (cr : R ≅ R₂ ⋙ R₁)
    (h : ∀ M : C e,
      cp.hom.app (J.obj M) ≫ P₁.map (a₂.app M) ≫ a₁.app (R₂.obj M) =
        ao.app M ≫ K.map (cr.hom.app M)) :
    Functor.whiskerLeft (twFunctor C J)
        (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso cp ≪≫
          Functor.whiskeringRightObjCompIso P₂ P₁).hom) ≫
      (Functor.associator (twFunctor C J) (twFunctor C P₂) (twFunctor C P₁)).inv ≫
      Functor.whiskerRight
        (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ J P₂ R₂ L a₂)
        (twFunctor C P₁) ≫
      (Functor.associator (twFunctor C R₂) (twFunctor C L) (twFunctor C P₁)).hom ≫
      Functor.whiskerLeft (twFunctor C R₂)
        (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ L P₁ R₁ K a₁) ≫
      (Functor.associator (twFunctor C R₂) (twFunctor C R₁) (twFunctor C K)).inv =
    Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ J P R K ao ≫
      Functor.whiskerRight
        (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso cr ≪≫
          Functor.whiskeringRightObjCompIso R₂ R₁).hom) (twFunctor C K) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    termwiseComposite_app_app, termwiseToComp_app_app,
    twFunctor, Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map,
    Functor.comp_obj, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.id_app, Category.id_comp, Category.comp_id] using h (M.obj n)

private theorem horizontalTowerLaw {a c e b d f : I}
    (K : C a ⥤ C b) (L : C b ⥤ C e) (KL : C a ⥤ C e)
    (V : C c ⥤ C d) (J : C d ⥤ C f) (VJ : C c ⥤ C f)
    (R : C c ⥤ C a) (P : C d ⥤ C b) (Q : C f ⥤ C e)
    (a₁ : V ⋙ P ⟶ R ⋙ K) (a₂ : J ⋙ Q ⟶ P ⋙ L)
    (ao : VJ ⋙ Q ⟶ R ⋙ KL) (ci : V ⋙ J ⟶ VJ) (ck : K ⋙ L ⟶ KL)
    (h : ∀ M : C c,
      Q.map (ci.app M) ≫ ao.app M =
        a₂.app (V.obj M) ≫ L.map (a₁.app M) ≫ ck.app (R.obj M)) :
    Functor.whiskerRight (termwiseCompHom V J VJ ci) (twFunctor C Q) ≫
        Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ VJ Q R KL ao =
      (Functor.associator (twFunctor C V) (twFunctor C J) (twFunctor C Q)).hom ≫
        Functor.whiskerLeft (twFunctor C V)
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ J Q P L a₂) ≫
        (Functor.associator (twFunctor C V) (twFunctor C P) (twFunctor C L)).inv ≫
        Functor.whiskerRight
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ V P R K a₁)
          (twFunctor C L) ≫
        (Functor.associator (twFunctor C R) (twFunctor C K) (twFunctor C L)).hom ≫
        Functor.whiskerLeft (twFunctor C R) (termwiseCompHom K L KL ck) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    termwiseComposite_app_app, termwiseComp_app_app,
    twFunctor, Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map,
    Functor.comp_obj, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.id_app, Category.id_comp, Category.comp_id] using h (M.obj n)

private abbrev twIso {a b c d : I}
    (F : C a ⥤ C b) (H : C b ⥤ C d) (G : C a ⥤ C c) (L : C c ⥤ C d)
    (e : F ⋙ H ≅ G ⋙ L) :=
  Functor.whiskeringRightObjCompIso F H ≪≫
    (Functor.whiskeringRight ℕᵒᵖ (C a) (C d)).mapIso e ≪≫
    (Functor.whiskeringRightObjCompIso G L).symm

private theorem twIso_inv_app_app {a b c d : I}
    (F : C a ⥤ C b) (H : C b ⥤ C d) (G : C a ⥤ C c) (L : C c ⥤ C d)
    (e : F ⋙ H ≅ G ⋙ L) (M : ℕᵒᵖ ⥤ C a) (n : ℕᵒᵖ) :
    ((twIso C F H G L e).inv.app M).app n = e.inv.app (M.obj n) := by
  simpa only [twIso, towerSquare] using towerSquare_inv_app_app F H G L e M n

private theorem cubeTowerLaw {v s w t v₁ s₁ w₁ t₁ : I}
    (K : C v ⥤ C w) (V : C s ⥤ C t) (R : C s ⥤ C v) (P : C t ⥤ C w)
    (K₁ : C v₁ ⥤ C w₁) (V₁ : C s₁ ⥤ C t₁)
    (R₁ : C s₁ ⥤ C v₁) (P₁ : C t₁ ⥤ C w₁)
    (A : C w ⥤ C w₁) (B' : C t ⥤ C t₁)
    (C' : C s ⥤ C s₁) (D : C v ⥤ C v₁)
    (ao : V ⋙ P ⟶ R ⋙ K) (a₁ : V₁ ⋙ P₁ ⟶ R₁ ⋙ K₁)
    (bk : K ⋙ A ≅ D ⋙ K₁) (bi : V ⋙ B' ≅ C' ⋙ V₁)
    (sp : B' ⋙ P₁ ≅ P ⋙ A) (sr : C' ⋙ R₁ ≅ R ⋙ D)
    (h : ∀ M : C s,
      sp.hom.app (V.obj M) ≫ A.map (ao.app M) ≫ bk.hom.app (R.obj M) ≫
          K₁.map (sr.inv.app M) =
        P₁.map (bi.hom.app M) ≫ a₁.app (C'.obj M)) :
    Functor.whiskerLeft (twFunctor C V) (twIso C B' P₁ P A sp).hom ≫
        (Functor.associator (twFunctor C V) (twFunctor C P) (twFunctor C A)).inv ≫
        Functor.whiskerRight
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ V P R K ao)
          (twFunctor C A) ≫
        (Functor.associator (twFunctor C R) (twFunctor C K) (twFunctor C A)).hom ≫
        Functor.whiskerLeft (twFunctor C R) (twIso C K A D K₁ bk).hom ≫
        (Functor.associator (twFunctor C R) (twFunctor C D) (twFunctor C K₁)).inv ≫
        Functor.whiskerRight (twIso C C' R₁ R D sr).inv (twFunctor C K₁) =
      (Functor.associator (twFunctor C V) (twFunctor C B') (twFunctor C P₁)).inv ≫
        Functor.whiskerRight (twIso C V B' C' V₁ bi).hom (twFunctor C P₁) ≫
        (Functor.associator (twFunctor C C') (twFunctor C V₁) (twFunctor C P₁)).hom ≫
        Functor.whiskerLeft (twFunctor C C')
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ V₁ P₁ R₁ K₁ a₁) ≫
        (Functor.associator (twFunctor C C') (twFunctor C R₁) (twFunctor C K₁)).inv := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    termwiseComposite_app_app, twIso_inv_app_app, twIso, termwiseSquare_app_app,
    twFunctor, Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map,
    Functor.comp_obj, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.id_app, Category.id_comp, Category.comp_id] using h (M.obj n)

end TowerLaws

end CategoryTheory.ExactDerivedPasting

namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

section PastingProofs

open CategoryTheory.ExactDerivedPasting
set_option linter.unusedSimpArgs false
attribute [local irreducible] Functor.leftAdjoint modulePullback
attribute [local irreducible] singleAlpha alpha beta gComp jComp squareG
attribute [local irreducible] moduleGComp moduleSquareG openBetaModule openBetaModuleJComp

attribute [local instance] clopenTowerAbelian towers_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private abbrev pastingCategories (X : Scheme.{u}) := Towers B X
private abbrev pastingG {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Word (pastingCategories B) Y X := .edge (ExactFunctor.of (towerPullback B f))
private abbrev pastingJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Word (pastingCategories B) U X := .edge (ExactFunctor.of (towerJ B j))

private theorem pastingCell_of_descent {X Y : Scheme.{u}}
    (P R : Word (pastingCategories B) X Y) (a : P.ordinary.obj ⟶ R.ordinary.obj)
    (d : P.derived ⟶ R.derived)
    (hd : ClopenProjectorDescent P.ordinary.obj R.ordinary.obj a
      (P.comparison.hom ≫ d ≫ R.comparison.inv)) :
    Word.cell (pastingCategories B) a = d := by
  have he :
      Localization.liftNatTrans DerivedCategory.Q
        (HomologicalComplex.quasiIso (Towers B X) (.up ℤ))
        (P.ordinary.obj.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (R.ordinary.obj.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        P.ordinary.obj.mapDerivedCategory R.ordinary.obj.mapDerivedCategory
        (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (.up ℤ))
          DerivedCategory.Q) = P.comparison.hom ≫ d ≫ R.comparison.inv := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (Towers B X) (.up ℤ))
    intro K
    apply (cancel_mono (R.ordinary.obj.mapDerivedCategoryFactors.hom.app K)).mp
    have hP : Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso (Towers B X) (.up ℤ))
        (P.ordinary.obj.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        P.ordinary.obj.mapDerivedCategory = P.ordinary.obj.mapDerivedCategoryFactors := rfl
    have hR : Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso (Towers B X) (.up ℤ))
        (R.ordinary.obj.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        R.ordinary.obj.mapDerivedCategory = R.ordinary.obj.mapDerivedCategoryFactors := rfl
    rw [Localization.liftNatTrans_app]
    simpa only [hP, hR, Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id] using (hd K).symm
  unfold Word.cell
  rw [he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem pastingAlpha {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    Word.cell (pastingCategories B)
      (P := .comp (pastingJ B i) (pastingG B p))
      (R := .comp (pastingG B r) (pastingJ B k))
      (towerAlpha B k r p i h) = alpha B k r p i h := by
  apply pastingCell_of_descent B (X := S) (Y := W)
  simpa only [Word.comparison, Word.ordinary, Word.derived, ExactFunctor.of_fst, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Iso.refl_hom, Iso.refl_inv, Functor.whiskerLeft_id', Functor.whiskerRight_id',
    Category.comp_id, Category.id_comp, Iso.symm_hom, Iso.symm_inv] using
    alpha_eq_localized_singleAlpha B k r p i h

private theorem pastingGComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Word.cell (pastingCategories B)
      (P := pastingG B (f ≫ g)) (R := .comp (pastingG B g) (pastingG B f))
      (towerGComp B f g).hom = (gComp B f g).hom := by
  simp only [Word.cell, Word.comparison, Word.ordinary, Word.derived, ExactFunctor.of_fst, gComp,
    Iso.refl_inv, Iso.refl_hom, Iso.trans_hom, Iso.trans_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_id', Functor.whiskerLeft_id', Category.comp_id, Category.id_comp]
  simp only [Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom,
    Functor.isoWhiskerRight_hom]
  rfl

private theorem pastingJComp {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    Word.cell (pastingCategories B)
      (P := .comp (pastingJ B j) (pastingJ B k)) (R := pastingJ B (j ≫ k))
      (termwiseCompHom (moduleJ B j) (moduleJ B k) (moduleJ B (j ≫ k))
        (openBetaModuleJComp B j k).hom) = (jComp B j k).hom := by
  exact @genericCompCell Scheme.{u} (pastingCategories B)
    (fun X ↦ inferInstanceAs (Category.{u + 1} (Towers B X)))
    (fun X ↦ clopenTowerAbelian B X) (fun X ↦ towers_hasDerivedCategory B X) U V X
    (ExactFunctor.of (towerJ B j)) (ExactFunctor.of (towerJ B k))
    (ExactFunctor.of (towerJ B (j ≫ k))) _ _ (jComp_fac B j k)

private theorem pastingBeta {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    Word.cell (pastingCategories B)
      (P := .comp (pastingJ B j) (pastingG B g))
      (R := .comp (pastingG B a) (pastingJ B j'))
      (openBetaTower B a j' j g w sq).hom = (beta B a j' j g w sq).hom := by
  exact @genericSquareCell Scheme.{u} (pastingCategories B)
    (fun X ↦ inferInstanceAs (Category.{u + 1} (Towers B X)))
    (fun X ↦ clopenTowerAbelian B X) (fun X ↦ towers_hasDerivedCategory B X) U X X' U'
    (ExactFunctor.of (towerJ B j)) (ExactFunctor.of (towerPullback B g))
    (ExactFunctor.of (towerPullback B a)) (ExactFunctor.of (towerJ B j')) _ _
    (beta_fac B a j' j g w sq)

private theorem pastingSquare {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    Word.cell (pastingCategories B)
      (P := .comp (pastingG B i) (pastingG B r))
      (R := .comp (pastingG B p) (pastingG B k))
      (towerSquare (modulePullback B i) (modulePullback B r)
        (modulePullback B p) (modulePullback B k) (moduleSquareG B k r p i h)).hom =
      (squareG B k r p i h).hom := by
  exact @genericSquareCell Scheme.{u} (pastingCategories B)
    (fun X ↦ inferInstanceAs (Category.{u + 1} (Towers B X)))
    (fun X ↦ clopenTowerAbelian B X) (fun X ↦ towers_hasDerivedCategory B X) T S V W
    (ExactFunctor.of (towerPullback B i)) (ExactFunctor.of (towerPullback B r))
    (ExactFunctor.of (towerPullback B p)) (ExactFunctor.of (towerPullback B k)) _ _
    (squareCompatible_of_eq (towerPullback B i) (towerPullback B r)
      (towerPullback B p) (towerPullback B k) _ _ (Iso.ext (squareG_lift B k r p i h)))

private theorem pastingSquareInv {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    Word.cell (pastingCategories B)
      (P := .comp (pastingG B p) (pastingG B k))
      (R := .comp (pastingG B i) (pastingG B r))
      (towerSquare (modulePullback B i) (modulePullback B r)
        (modulePullback B p) (modulePullback B k) (moduleSquareG B k r p i h)).inv =
      (squareG B k r p i h).inv := by
  have hg : squareG B k r p i h = Functor.mapDerivedCategorySquareIso
      (towerSquare (modulePullback B i) (modulePullback B r)
        (modulePullback B p) (modulePullback B k) (moduleSquareG B k r p i h)) :=
    Iso.ext (squareG_lift B k r p i h)
  have hn := (congrArg Iso.symm hg).trans
    (@genericSquareIsoSymm Scheme.{u} (pastingCategories B)
      (fun X ↦ inferInstanceAs (Category.{u + 1} (Towers B X)))
      (fun X ↦ clopenTowerAbelian B X) (fun X ↦ towers_hasDerivedCategory B X) T S V W
      (ExactFunctor.of (towerPullback B i)) (ExactFunctor.of (towerPullback B r))
      (ExactFunctor.of (towerPullback B p)) (ExactFunctor.of (towerPullback B k))
      (towerSquare (modulePullback B i) (modulePullback B r)
        (modulePullback B p) (modulePullback B k) (moduleSquareG B k r p i h)))
  exact @genericSquareCell Scheme.{u} (pastingCategories B)
    (fun X ↦ inferInstanceAs (Category.{u + 1} (Towers B X)))
    (fun X ↦ clopenTowerAbelian B X) (fun X ↦ towers_hasDerivedCategory B X) T W V S
    (ExactFunctor.of (towerPullback B p)) (ExactFunctor.of (towerPullback B k))
    (ExactFunctor.of (towerPullback B i)) (ExactFunctor.of (towerPullback B r)) _ _
    (squareCompatible_of_eq (towerPullback B p) (towerPullback B k)
      (towerPullback B i) (towerPullback B r) _ _ hn)

end PastingProofs

end AlgebraicGeometry.ProEtale.StrictTower
