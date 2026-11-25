/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenArrowFactors
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearAlphaRestriction
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearPullbackCubeCoherence

/-!
# Pullback compatibility of the intrinsic semilinear alpha

Source: Stacks Project, Tag 0F7F, alpha-level open case, and the agent-written
extension to arbitrary strict semilinear systems
(blueprint: lem-sf-semilinear-alpha-pullback).

The ordinary system cube is stated first. Its exact localization is the derived
cube, prior to taking any proper direct-image mate. The auxiliary isomorphisms
only localize the dependency's specified ordinary comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w x
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local irreducible] moduleAlpha moduleBeta moduleSquareG moduleGComp moduleJComp
  Functor.leftAdjoint
  Functor.mapDerivedCategory Localization.liftNatTrans

attribute [local instance] moduleJAdj_unit_isIso moduleOpenToP_isIso

-- Detection uses the source left adjunction and the target right adjunction.
private theorem hom_ext_two_adjunctions
    {A B D : Type*} [Category A] [Category B] [Category D]
    {L : A ⥤ B} {G : B ⥤ A} {T : A ⥤ D} {S : D ⥤ A}
    (adj₁ : L ⊣ G) (adj₂ : T ⊣ S)
    {X : A} {F Y : B} {N : D} (src : F ≅ L.obj X) (tgt : G.obj Y ≅ S.obj N)
    {f g : F ⟶ Y} (h : T.map (G.map f) = T.map (G.map g)) : f = g := by
  have hg : G.map f = G.map g := by
    apply (cancel_mono tgt.hom).mp
    apply (adj₂.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, h]
  apply (cancel_epi src.inv).mp
  apply (adj₁.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, hg]

private theorem module_clopen_factor_hom_ext
    {U T V : Scheme.{u}} (s : U ⟶ T) (b : T ⟶ V) (k : U ⟶ V)
    [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion b] [IsOpenImmersion k] (e : s ≫ b = k)
    {F : Modules R φ V} {A : Modules R φ T} {N : Modules R φ U}
    (src : F ≅ (extension R φ b).obj A)
    {f g : F ⟶ (extension R φ k).obj N}
    (h : (pull R φ k).map f = (pull R φ k).map g) : f = g := by
  let ej : extension R φ k ≅ extension R φ s ⋙ extension R φ b :=
    (moduleJCongr R φ e).symm ≪≫ (moduleJComp R φ s b).symm
  let eg : pull R φ k ≅ pull R φ b ⋙ pull R φ s :=
    eqToIso (congrArg (pull R φ) e.symm) ≪≫ moduleGComp R φ s b
  let tgt : (pull R φ b).obj ((extension R φ k).obj N) ≅ (push R φ s).obj N :=
    (pull R φ b).mapIso (ej.app N) ≪≫
      (asIso ((moduleJAdj R φ b).unit.app ((extension R φ s).obj N))).symm ≪≫
        (asIso (moduleOpenToP R φ s)).app N
  apply hom_ext_two_adjunctions (moduleJAdj R φ b) (moduleAdj R φ s) src tgt
  change (pull R φ b ⋙ pull R φ s).map f = (pull R φ b ⋙ pull R φ s).map g
  apply (cancel_epi (eg.hom.app F)).mp
  rw [← eg.hom.naturality, ← eg.hom.naturality, h]

private theorem moduleBeta_restriction {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) (M : Modules R φ U) :
    (pull R φ j').map ((moduleBeta R φ a j' j g h hsq).hom.app M) ≫
        inv ((moduleJAdj R φ j').unit.app ((pull R φ a).obj M)) =
      (moduleSquareG R φ a j' j g h).hom.app ((extension R φ j).obj M) ≫
        (pull R φ a).map (inv ((moduleJAdj R φ j).unit.app M)) := by
  have := moduleJAdj_unit_isIso R φ j
  have := moduleJAdj_unit_isIso R φ j'
  have hu : (moduleJAdj R φ j').unit.app ((pull R φ a).obj M) ≫
      (pull R φ j').map ((moduleBeta R φ a j' j g h hsq).inv.app M) =
    (pull R φ a).map ((moduleJAdj R φ j).unit.app M) ≫
      (moduleSquareG R φ a j' j g h).inv.app ((extension R φ j).obj M) := by
    have hh := ((moduleJAdj R φ j').homEquiv _ _).apply_symm_apply
      ((pull R φ a).map ((moduleJAdj R φ j).unit.app M) ≫
        (moduleSquareG R φ a j' j g h).inv.app ((extension R φ j).obj M))
    simpa only [Adjunction.homEquiv_unit, moduleBeta, Iso.symm_hom,
      Iso.symm_inv, asIso_hom, moduleBetaInv, moduleBetaInvApp,
      Functor.id_obj, Functor.comp_obj] using hh
  let u := asIso ((moduleJAdj R φ j').unit.app ((pull R φ a).obj M))
  let v := (pull R φ j').mapIso ((moduleBeta R φ a j' j g h hsq).app M)
  let z := (moduleSquareG R φ a j' j g h).app ((extension R φ j).obj M)
  let w := (pull R φ a).mapIso (asIso ((moduleJAdj R φ j).unit.app M))
  have he : u ≪≫ v.symm = w ≪≫ z.symm := Iso.ext hu
  have hi := congrArg (fun e ↦ e.inv) he
  simpa only [u, v, z, w, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom, asIso_inv,
    Iso.app_hom] using hi

private theorem exactFunctor_of_additive
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (ExactFunctor.of F).obj.Additive := by
  simpa only [ExactFunctor.of_fst] using (inferInstance : F.Additive)

attribute [local instance] exactFunctor_of_additive

private theorem cell_pair
    {ι : Type*} (C : ι → Type*) [∀ a, Category (C a)] [∀ a, Abelian (C a)]
    [∀ a, HasDerivedCategory (C a)] {a b c d : ι}
    (F : C a ⥤ₑ C b) (G : C b ⥤ₑ C d)
    (H : C a ⥤ₑ C c) (K : C c ⥤ₑ C d)
    [F.obj.Additive] [G.obj.Additive] [H.obj.Additive] [K.obj.Additive]
    (t : F.obj ⋙ G.obj ⟶ H.obj ⋙ K.obj) :
    ExactDerivedPasting.Word.cell C
      (P := .comp (.edge F) (.edge G)) (R := .comp (.edge H) (.edge K)) t =
      localizedArrow F.obj G.obj H.obj K.obj t := by
  simp only [ExactDerivedPasting.Word.cell, ExactDerivedPasting.Word.comparison,
    ExactDerivedPasting.Word.ordinary, ExactDerivedPasting.Word.derived,
    localizedArrow, Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl,
    Iso.trans_refl, Iso.symm_hom, Iso.symm_inv]

-- Localize the entire ordinary equality as a finite pasting of exact functors.
private theorem localize_cube
    {ι : Type*} [Finite ι] (C : ι → Type*) [∀ n, Category (C n)] [∀ n, Abelian (C n)]
    [∀ n, HasDerivedCategory (C n)]
    (v₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : ι)
    (If : C v₀ ⥤ₑ C v₁) [If.obj.Additive]
    (Pf : C v₁ ⥤ₑ C v₂) [Pf.obj.Additive]
    (Kf : C v₃ ⥤ₑ C v₂) [Kf.obj.Additive]
    (Qf : C v₀ ⥤ₑ C v₃) [Qf.obj.Additive]
    (I₁f : C v₄ ⥤ₑ C v₅) [I₁f.obj.Additive]
    (P₁f : C v₅ ⥤ₑ C v₆) [P₁f.obj.Additive]
    (K₁f : C v₇ ⥤ₑ C v₆) [K₁f.obj.Additive]
    (Q₁f : C v₄ ⥤ₑ C v₇) [Q₁f.obj.Additive]
    (Af : C v₂ ⥤ₑ C v₆) [Af.obj.Additive]
    (Hf : C v₁ ⥤ₑ C v₅) [Hf.obj.Additive]
    (C₀f : C v₀ ⥤ₑ C v₄) [C₀f.obj.Additive]
    (Df : C v₃ ⥤ₑ C v₇) [Df.obj.Additive]
    (al0 : If.obj ⋙ Pf.obj ⟶ Qf.obj ⋙ Kf.obj)
    (al₁0 : I₁f.obj ⋙ P₁f.obj ⟶ Q₁f.obj ⋙ K₁f.obj)
    (bi0 : If.obj ⋙ Hf.obj ⟶ C₀f.obj ⋙ I₁f.obj)
    (bk0 : Kf.obj ⋙ Af.obj ⟶ Df.obj ⋙ K₁f.obj)
    (gp0 : Hf.obj ⋙ P₁f.obj ⟶ Pf.obj ⋙ Af.obj)
    (gr0 : Qf.obj ⋙ Df.obj ⟶ C₀f.obj ⋙ Q₁f.obj)
    (hOrd : ∀ N : C v₀, P₁f.obj.map (bi0.app N) ≫ al₁0.app (C₀f.obj.obj N) =
      gp0.app (If.obj.obj N) ≫ Af.obj.map (al0.app N) ≫ bk0.app (Qf.obj.obj N) ≫
        K₁f.obj.map (gr0.app N)) (M : DerivedCategory (C v₀)) :
    P₁f.obj.mapDerivedCategory.map ((localizedArrow If.obj Hf.obj C₀f.obj I₁f.obj bi0).app M) ≫
        (localizedArrow I₁f.obj P₁f.obj Q₁f.obj K₁f.obj al₁0).app
          (C₀f.obj.mapDerivedCategory.obj M) =
      (localizedArrow Hf.obj P₁f.obj Pf.obj Af.obj gp0).app (If.obj.mapDerivedCategory.obj M) ≫
        Af.obj.mapDerivedCategory.map ((localizedArrow If.obj Pf.obj Qf.obj Kf.obj al0).app M) ≫
        (localizedArrow Kf.obj Af.obj Df.obj K₁f.obj bk0).app (Qf.obj.mapDerivedCategory.obj M) ≫
        K₁f.obj.mapDerivedCategory.map
          ((localizedArrow Qf.obj Df.obj C₀f.obj Q₁f.obj gr0).app M) := by
  let I : ExactDerivedPasting.Word C v₀ v₁ := .edge If
  let P : ExactDerivedPasting.Word C v₁ v₂ := .edge Pf
  let K : ExactDerivedPasting.Word C v₃ v₂ := .edge Kf
  let Q : ExactDerivedPasting.Word C v₀ v₃ := .edge Qf
  let I₁ : ExactDerivedPasting.Word C v₄ v₅ := .edge I₁f
  let P₁ : ExactDerivedPasting.Word C v₅ v₆ := .edge P₁f
  let K₁ : ExactDerivedPasting.Word C v₇ v₆ := .edge K₁f
  let Q₁ : ExactDerivedPasting.Word C v₄ v₇ := .edge Q₁f
  let A : ExactDerivedPasting.Word C v₂ v₆ := .edge Af
  let H : ExactDerivedPasting.Word C v₁ v₅ := .edge Hf
  let C₀ : ExactDerivedPasting.Word C v₀ v₄ := .edge C₀f
  let D : ExactDerivedPasting.Word C v₃ v₇ := .edge Df
  let al : ExactDerivedPasting.Expression C (.comp I P) (.comp Q K) :=
    .cell al0
  let al₁ : ExactDerivedPasting.Expression C (.comp I₁ P₁) (.comp Q₁ K₁) :=
    .cell al₁0
  let bi : ExactDerivedPasting.Expression C (.comp I H) (.comp C₀ I₁) :=
    .cell bi0
  let bk : ExactDerivedPasting.Expression C (.comp K A) (.comp D K₁) :=
    .cell bk0
  let gp : ExactDerivedPasting.Expression C (.comp H P₁) (.comp P A) :=
    .cell gp0
  let gr : ExactDerivedPasting.Expression C (.comp Q D) (.comp C₀ Q₁) :=
    .cell gr0
  let left : ExactDerivedPasting.Expression C
      (.comp (.comp I H) P₁) (.comp C₀ (.comp Q₁ K₁)) :=
    .vcomp (.output bi P₁) (.vcomp (.assoc C₀ I₁ P₁) (.input C₀ al₁))
  let right : ExactDerivedPasting.Expression C
      (.comp (.comp I H) P₁) (.comp C₀ (.comp Q₁ K₁)) :=
    .vcomp (.assoc I H P₁) <| .vcomp (.input I gp) <|
      .vcomp (.assocInv I P A) <| .vcomp (.output al A) <|
      .vcomp (.assoc Q K A) <| .vcomp (.input Q bk) <|
      .vcomp (.assocInv Q D K₁) <| .vcomp (.output gr K₁) (.assoc C₀ Q₁ K₁)
  have ho : left.ordinary = right.ordinary := by
    apply NatTrans.ext
    funext N
    simpa only [left, right, al, al₁, bi, bk, gp, gr,
      ExactDerivedPasting.Expression.ordinary, ExactDerivedPasting.Word.ordinary,
      I, P, K, Q, I₁, P₁, K₁, Q₁, A, H, C₀, D, ExactFunctor.of_fst,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using
      hOrd N
  have hd := (ExactDerivedPasting.exact_derived_transformation_pasting C).2.1 left right ho
  have hm := congrArg (fun t ↦ t.app M) hd
  simpa only [left, right, al, al₁, bi, bk, gp, gr,
    ExactDerivedPasting.Expression.derived, cell_pair,
    ExactDerivedPasting.Word.derived, ExactDerivedPasting.Word.ordinary,
    I, P, K, Q, I₁, P₁, K₁, Q₁, A, H, C₀, D, ExactFunctor.of_fst,
    localizedArrow,
    Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom,
    Localization.liftNatIso_inv, NatIso.mapHomologicalComplex,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hm

private theorem localize_cube_types
    (C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇ : Type v)
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Category.{w} C₄] [Category.{w} C₅] [Category.{w} C₆] [Category.{w} C₇]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [Abelian C₄] [Abelian C₅] [Abelian C₆] [Abelian C₇]
    [HasDerivedCategory.{x} C₀] [HasDerivedCategory.{x} C₁]
    [HasDerivedCategory.{x} C₂] [HasDerivedCategory.{x} C₃]
    [HasDerivedCategory.{x} C₄] [HasDerivedCategory.{x} C₅]
    [HasDerivedCategory.{x} C₆] [HasDerivedCategory.{x} C₇]
    (If : C₀ ⥤ₑ C₁) [If.obj.Additive]
    (Pf : C₁ ⥤ₑ C₂) [Pf.obj.Additive]
    (Kf : C₃ ⥤ₑ C₂) [Kf.obj.Additive]
    (Qf : C₀ ⥤ₑ C₃) [Qf.obj.Additive]
    (I₁f : C₄ ⥤ₑ C₅) [I₁f.obj.Additive]
    (P₁f : C₅ ⥤ₑ C₆) [P₁f.obj.Additive]
    (K₁f : C₇ ⥤ₑ C₆) [K₁f.obj.Additive]
    (Q₁f : C₄ ⥤ₑ C₇) [Q₁f.obj.Additive]
    (Af : C₂ ⥤ₑ C₆) [Af.obj.Additive]
    (Hf : C₁ ⥤ₑ C₅) [Hf.obj.Additive]
    (C₀f : C₀ ⥤ₑ C₄) [C₀f.obj.Additive]
    (Df : C₃ ⥤ₑ C₇) [Df.obj.Additive]
    (al0 : If.obj ⋙ Pf.obj ⟶ Qf.obj ⋙ Kf.obj)
    (al₁0 : I₁f.obj ⋙ P₁f.obj ⟶ Q₁f.obj ⋙ K₁f.obj)
    (bi0 : If.obj ⋙ Hf.obj ⟶ C₀f.obj ⋙ I₁f.obj)
    (bk0 : Kf.obj ⋙ Af.obj ⟶ Df.obj ⋙ K₁f.obj)
    (gp0 : Hf.obj ⋙ P₁f.obj ⟶ Pf.obj ⋙ Af.obj)
    (gr0 : Qf.obj ⋙ Df.obj ⟶ C₀f.obj ⋙ Q₁f.obj)
    (hOrd : ∀ N : C₀, P₁f.obj.map (bi0.app N) ≫ al₁0.app (C₀f.obj.obj N) =
      gp0.app (If.obj.obj N) ≫ Af.obj.map (al0.app N) ≫ bk0.app (Qf.obj.obj N) ≫
        K₁f.obj.map (gr0.app N)) (M : DerivedCategory (C₀)) :
    P₁f.obj.mapDerivedCategory.map ((localizedArrow If.obj Hf.obj C₀f.obj I₁f.obj bi0).app M) ≫
        (localizedArrow I₁f.obj P₁f.obj Q₁f.obj K₁f.obj al₁0).app
          (C₀f.obj.mapDerivedCategory.obj M) =
      (localizedArrow Hf.obj P₁f.obj Pf.obj Af.obj gp0).app (If.obj.mapDerivedCategory.obj M) ≫
        Af.obj.mapDerivedCategory.map ((localizedArrow If.obj Pf.obj Qf.obj Kf.obj al0).app M) ≫
        (localizedArrow Kf.obj Af.obj Df.obj K₁f.obj bk0).app (Qf.obj.mapDerivedCategory.obj M) ≫
        K₁f.obj.mapDerivedCategory.map
          ((localizedArrow Qf.obj Df.obj C₀f.obj Q₁f.obj gr0).app M) := by
  let C : Fin 8 → Type _ := ![C₀, C₁, C₂, C₃, C₄, C₅, C₆, C₇]
  let _ : ∀ n, Category (C n) :=
      (Fin.cases (inferInstance : Category C₀)
      (Fin.cases (inferInstance : Category C₁)
      (Fin.cases (inferInstance : Category C₂)
      (Fin.cases (inferInstance : Category C₃)
      (Fin.cases (inferInstance : Category C₄)
      (Fin.cases (inferInstance : Category C₅)
      (Fin.cases (inferInstance : Category C₆)
        (fun i : Fin 1 ↦ Fin.cases (inferInstance : Category C₇) (fun e ↦ Fin.elim0 e) i))))))))
  let _ : ∀ n, Abelian (C n) :=
      (Fin.cases (inferInstance : Abelian C₀)
      (Fin.cases (inferInstance : Abelian C₁)
      (Fin.cases (inferInstance : Abelian C₂)
      (Fin.cases (inferInstance : Abelian C₃)
      (Fin.cases (inferInstance : Abelian C₄)
      (Fin.cases (inferInstance : Abelian C₅)
      (Fin.cases (inferInstance : Abelian C₆)
        (fun i : Fin 1 ↦ Fin.cases (inferInstance : Abelian C₇) (fun e ↦ Fin.elim0 e) i))))))))
  let _ : ∀ n, HasDerivedCategory (C n) :=
      (Fin.cases (inferInstance : HasDerivedCategory C₀)
      (Fin.cases (inferInstance : HasDerivedCategory C₁)
      (Fin.cases (inferInstance : HasDerivedCategory C₂)
      (Fin.cases (inferInstance : HasDerivedCategory C₃)
      (Fin.cases (inferInstance : HasDerivedCategory C₄)
      (Fin.cases (inferInstance : HasDerivedCategory C₅)
      (Fin.cases (inferInstance : HasDerivedCategory C₆)
        (fun i : Fin 1 ↦ Fin.cases (inferInstance : HasDerivedCategory C₇)
          (fun e ↦ Fin.elim0 e) i))))))))
  have hh := localize_cube C 0 1 2 3 4 5 6 7
    If Pf Kf Qf I₁f P₁f K₁f Q₁f Af Hf C₀f Df al0 al₁0 bi0 bk0 gp0 gr0 hOrd M
  exact hh

private theorem localize_cube_functors
    (C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇ : Type v)
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Category.{w} C₄] [Category.{w} C₅] [Category.{w} C₆] [Category.{w} C₇]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [Abelian C₄] [Abelian C₅] [Abelian C₆] [Abelian C₇]
    [HasDerivedCategory.{x} C₀] [HasDerivedCategory.{x} C₁]
    [HasDerivedCategory.{x} C₂] [HasDerivedCategory.{x} C₃]
    [HasDerivedCategory.{x} C₄] [HasDerivedCategory.{x} C₅]
    [HasDerivedCategory.{x} C₆] [HasDerivedCategory.{x} C₇]
    (If : C₀ ⥤ C₁) [If.Additive]
    [PreservesFiniteLimits If] [PreservesFiniteColimits If]
    (Pf : C₁ ⥤ C₂) [Pf.Additive]
    [PreservesFiniteLimits Pf] [PreservesFiniteColimits Pf]
    (Kf : C₃ ⥤ C₂) [Kf.Additive]
    [PreservesFiniteLimits Kf] [PreservesFiniteColimits Kf]
    (Qf : C₀ ⥤ C₃) [Qf.Additive]
    [PreservesFiniteLimits Qf] [PreservesFiniteColimits Qf]
    (I₁f : C₄ ⥤ C₅) [I₁f.Additive]
    [PreservesFiniteLimits I₁f] [PreservesFiniteColimits I₁f]
    (P₁f : C₅ ⥤ C₆) [P₁f.Additive]
    [PreservesFiniteLimits P₁f] [PreservesFiniteColimits P₁f]
    (K₁f : C₇ ⥤ C₆) [K₁f.Additive]
    [PreservesFiniteLimits K₁f] [PreservesFiniteColimits K₁f]
    (Q₁f : C₄ ⥤ C₇) [Q₁f.Additive]
    [PreservesFiniteLimits Q₁f] [PreservesFiniteColimits Q₁f]
    (Af : C₂ ⥤ C₆) [Af.Additive]
    [PreservesFiniteLimits Af] [PreservesFiniteColimits Af]
    (Hf : C₁ ⥤ C₅) [Hf.Additive]
    [PreservesFiniteLimits Hf] [PreservesFiniteColimits Hf]
    (C₀f : C₀ ⥤ C₄) [C₀f.Additive]
    [PreservesFiniteLimits C₀f] [PreservesFiniteColimits C₀f]
    (Df : C₃ ⥤ C₇) [Df.Additive]
    [PreservesFiniteLimits Df] [PreservesFiniteColimits Df]
    (al0 : If ⋙ Pf ⟶ Qf ⋙ Kf)
    (al₁0 : I₁f ⋙ P₁f ⟶ Q₁f ⋙ K₁f)
    (bi0 : If ⋙ Hf ⟶ C₀f ⋙ I₁f)
    (bk0 : Kf ⋙ Af ⟶ Df ⋙ K₁f)
    (gp0 : Hf ⋙ P₁f ⟶ Pf ⋙ Af)
    (gr0 : Qf ⋙ Df ⟶ C₀f ⋙ Q₁f)
    (hOrd : ∀ N : C₀, P₁f.map (bi0.app N) ≫ al₁0.app (C₀f.obj N) =
      gp0.app (If.obj N) ≫ Af.map (al0.app N) ≫ bk0.app (Qf.obj N) ≫
        K₁f.map (gr0.app N)) (M : DerivedCategory (C₀)) :
    P₁f.mapDerivedCategory.map ((localizedArrow If Hf C₀f I₁f bi0).app M) ≫
        (localizedArrow I₁f P₁f Q₁f K₁f al₁0).app
          (C₀f.mapDerivedCategory.obj M) =
      (localizedArrow Hf P₁f Pf Af gp0).app (If.mapDerivedCategory.obj M) ≫
        Af.mapDerivedCategory.map ((localizedArrow If Pf Qf Kf al0).app M) ≫
        (localizedArrow Kf Af Df K₁f bk0).app (Qf.mapDerivedCategory.obj M) ≫
        K₁f.mapDerivedCategory.map
          ((localizedArrow Qf Df C₀f Q₁f gr0).app M) := by
  exact localize_cube_types C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇
    (ExactFunctor.of If)
    (ExactFunctor.of Pf)
    (ExactFunctor.of Kf)
    (ExactFunctor.of Qf)
    (ExactFunctor.of I₁f)
    (ExactFunctor.of P₁f)
    (ExactFunctor.of K₁f)
    (ExactFunctor.of Q₁f)
    (ExactFunctor.of Af)
    (ExactFunctor.of Hf)
    (ExactFunctor.of C₀f)
    (ExactFunctor.of Df)
    al0 al₁0 bi0 bk0 gp0 gr0 hOrd M

/-- Exact localization of the specified unit-normalized open comparison.
Source: Stacks, Tags 09AE and 0F7F (blueprint: lem-sf-semilinear-alpha-pullback).
This is the actual ordinary moduleBeta localized, with the standard composition
isomorphisms; no derived comparison is selected independently. -/
def alphaPullbackBeta {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) : J R φ j ⋙ G R φ g ≅ G R φ a ⋙ J R φ j' :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (moduleBeta R φ a j' j g h hsq) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Exact localization of the specified inverse-image square compositor.
Source: Stacks, Tags 07A7 and 0F7F (blueprint: lem-sf-semilinear-alpha-pullback).
The square comparison is induced by moduleGComp, hence by the section-normalized
ordinary direct-image comparison, with its prescribed adjunction units. -/
def alphaPullbackSquareG {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (h : k ≫ p = r ≫ i) : G R φ i ⋙ G R φ r ≅ G R φ p ⋙ G R φ k :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (moduleSquareG R φ k r p i h) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

private theorem localizedArrow_iso_hom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K] (e : F ⋙ G ≅ H ⋙ K) :
    localizedArrow F G H K e.hom =
      (Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso H K).symm).hom := by
  simp only [localizedArrow, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom,
    NatIso.mapHomologicalComplex, Functor.isoWhiskerRight_hom]

private theorem localizedArrow_iso_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K] (e : H ⋙ K ≅ F ⋙ G) :
    localizedArrow F G H K e.inv =
      (Functor.mapDerivedCategoryCompIso H K ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso F G).symm).inv := by
  simp only [localizedArrow, Iso.trans_inv, Iso.symm_inv,
    Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_inv,
    NatIso.mapHomologicalComplex, Functor.isoWhiskerRight_inv, Category.assoc]

private theorem alpha_localized
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (w : k ≫ p = r ≫ i) :
    alpha R φ k r p i w =
      localizedArrow (extension R φ i) (pull R φ p) (pull R φ r) (extension R φ k)
        (moduleAlpha R φ k r p i w) := by
  rfl

private theorem beta_localized {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) :
    (alphaPullbackBeta R φ a j' j g h hsq).hom =
      localizedArrow (extension R φ j) (pull R φ g) (pull R φ a) (extension R φ j')
        (moduleBeta R φ a j' j g h hsq).hom := by
  exact (localizedArrow_iso_hom _ _ _ _ _).symm

private theorem square_localized {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (h : k ≫ p = r ≫ i) :
    (alphaPullbackSquareG R φ k r p i h).hom =
      localizedArrow (pull R φ i) (pull R φ r) (pull R φ p) (pull R φ k)
        (moduleSquareG R φ k r p i h).hom := by
  exact (localizedArrow_iso_hom _ _ _ _ _).symm

private theorem square_inv_localized {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (h : k ≫ p = r ≫ i) :
    (alphaPullbackSquareG R φ k r p i h).inv =
      localizedArrow (pull R φ p) (pull R φ k) (pull R φ i) (pull R φ r)
        (moduleSquareG R φ k r p i h).inv := by
  exact (localizedArrow_iso_inv _ _ _ _ _).symm

/-- The pullback cube already commutes on ordinary semilinear systems.
Source: Stacks, Tag 0F7F, alpha-level open case; agent-written semilinear extension
(blueprint: lem-sf-semilinear-alpha-pullback).
Proof (the node's seven steps):
1. Factor Q through T = V ×_Z W. The canonical lift s : U → T is clopen.
   Base change gives s₁ : U₁ → T₁, its clopen image, and its complementary open.
2. For an ordinary system M use the two cartesian open comparisons to write the
   common source as b₁! q₁* c* M. The open-adjunction Hom bijection reduces
   equality to equality after restriction along b₁.
3. Transpose the defining open unit for moduleBeta. The triangle identity says
   its restriction is identity under the open-unit identifications.
4. The clopen modulePi is the direct-image unit followed by the inverse of the
   open-to-direct-image comparison. Its restriction is the open unit. Therefore
   restriction of moduleAlpha along k is r* applied to the inverse unit for i.
5. Restrict both cube paths along k₁. By steps 3 and 4 both give r₁* c* applied
   to the inverse unit for i. The specified compositors agree: their right
   adjoints are the same identity-on-sections direct-image comparison.
6. On the complement of s₁ the common target is zero. On the image the two
   restrictions agree by step 5. Sheaf uniqueness on this disjoint open cover,
   coefficientwise and compatibly with the transitions, gives the ordinary
   system equality. The Hom bijection in step 2 removes the restriction.
7. Apply the ordinary transformations degreewise to unbounded complexes and
   localize at quasi-isomorphisms. Exactness preserves quasi-isomorphisms and
   the localization universal property preserves the equality and composition.
   This gives the derived equality before any proper direct-image mate is taken.
-/
theorem moduleAlpha_baseChange
    {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
    (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
    (k₁ : U₁ ⟶ V₁) (i₁ : W₁ ⟶ Z₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁)
    (a : V₁ ⟶ V) (h : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (w : k ≫ p = r ≫ i) (w₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ h)
    (wp : a ≫ p = p₁ ≫ h) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i h)
    (sp : IsPullback a p₁ p h) (sr : IsPullback d r₁ r c)
    (M : Modules R φ W) :
    (pull R φ p₁).map ((moduleBeta R φ c i₁ i h wi si).hom.app M) ≫
        (moduleAlpha R φ k₁ r₁ p₁ i₁ w₁).app ((pull R φ c).obj M) =
      (moduleSquareG R φ a p₁ p h wp).hom.app ((extension R φ i).obj M) ≫
        (pull R φ a).map ((moduleAlpha R φ k r p i w).app M) ≫
        (moduleBeta R φ d k₁ k a wk sk).hom.app ((pull R φ r).obj M) ≫
        (extension R φ k₁).map ((moduleSquareG R φ d r₁ r c wr).inv.app M) := by
  have _sp := sp
  have _sr := sr
  let b := pullback.fst p₁ i₁
  let q := pullback.snd p₁ i₁
  let s := StrictTower.squareLift k₁ r₁ p₁ i₁ w₁
  let src : (pull R φ p₁).obj ((pull R φ h).obj ((extension R φ i).obj M)) ≅
      (extension R φ b).obj ((pull R φ q).obj ((pull R φ c).obj M)) :=
    (pull R φ p₁).mapIso ((moduleBeta R φ c i₁ i h wi si).app M) ≪≫
      (moduleBeta R φ q b i₁ p₁ pullback.condition.symm
        (IsPullback.of_hasPullback p₁ i₁).flip).app ((pull R φ c).obj M)
  apply module_clopen_factor_hom_ext R φ s b k₁ (pullback.lift_fst k₁ r₁ w₁) src
  apply (cancel_mono (inv ((moduleJAdj R φ k₁).unit.app
    ((pull R φ r₁).obj ((pull R φ c).obj M))))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [moduleAlpha_restriction]
  have hn := (moduleSquareG R φ k₁ r₁ p₁ i₁ w₁).inv.naturality
    ((moduleBeta R φ c i₁ i h wi si).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    moduleBeta_restriction, Functor.map_comp]
  have hu := (asIso (moduleJAdj R φ k₁).unit).inv.naturality
    ((moduleSquareG R φ d r₁ r c wr).inv.app M)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj,
    asIso_inv, NatIso.isIso_inv_app] at hu
  rw [hu]
  slice_rhs 3 4 => rw [moduleBeta_restriction]
  have hk := (moduleSquareG R φ d k₁ k a wk).hom.naturality
    ((moduleAlpha R φ k r p i w).app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hk
  slice_rhs 2 3 => rw [hk]
  slice_rhs 3 4 => rw [← Functor.map_comp, moduleAlpha_restriction, Functor.map_comp]
  have hr := (moduleSquareG R φ d r₁ r c wr).inv.naturality
    (inv ((moduleJAdj R φ i).unit.app M))
  simp only [Functor.comp_map, Functor.comp_obj] at hr
  simp only [Functor.comp_obj, Functor.id_obj] at hr ⊢
  slice_rhs 4 5 => rw [hr]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ (pull R φ r₁).map ((pull R φ c).map
      (inv ((moduleJAdj R φ i).unit.app M))))
    (moduleSquareG_cube R φ k i r p k₁ i₁ r₁ p₁ a h c d
      w w₁ wk wi wp wr ((extension R φ i).obj M))

/-- The two displayed alpha cube paths agree after exact localization, on every
unbounded derived system, prior to taking any proper direct-image mate.
Source: Stacks, Tag 0F7F, alpha-level open case; agent-written semilinear extension
(blueprint: lem-sf-semilinear-alpha-pullback).
Proof (the node's seven steps):
1. Factor Q through T = V ×_Z W. The canonical lift s : U → T is clopen.
   Base change gives s₁ : U₁ → T₁, its clopen image, and its complementary open.
2. For an ordinary system M use the two cartesian open comparisons to write the
   common source as b₁! q₁* c* M. The open-adjunction Hom bijection reduces
   equality to equality after restriction along b₁.
3. Transpose the defining open unit for moduleBeta. The triangle identity says
   its restriction is identity under the open-unit identifications.
4. The clopen modulePi is the direct-image unit followed by the inverse of the
   open-to-direct-image comparison. Its restriction is the open unit. Therefore
   restriction of moduleAlpha along k is r* applied to the inverse unit for i.
5. Restrict both cube paths along k₁. By steps 3 and 4 both give r₁* c* applied
   to the inverse unit for i. The specified compositors agree: their right
   adjoints are the same identity-on-sections direct-image comparison.
6. On the complement of s₁ the common target is zero. On the image the two
   restrictions agree by step 5. Sheaf uniqueness on this disjoint open cover,
   coefficientwise and compatibly with the transitions, gives the ordinary
   system equality. The Hom bijection in step 2 removes the restriction.
7. Apply the ordinary transformations degreewise to unbounded complexes and
   localize at quasi-isomorphisms. Exactness preserves quasi-isomorphisms and
   the localization universal property preserves the equality and composition.
   This gives the derived equality before any proper direct-image mate is taken.
-/
theorem alpha_baseChange
    {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
    (k : U ⟶ V) (i : W ⟶ Z) (r : U ⟶ W) (p : V ⟶ Z)
    (k₁ : U₁ ⟶ V₁) (i₁ : W₁ ⟶ Z₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁)
    (a : V₁ ⟶ V) (h : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (w : k ≫ p = r ≫ i) (w₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ h)
    (wp : a ≫ p = p₁ ≫ h) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i h)
    (sp : IsPullback a p₁ p h) (sr : IsPullback d r₁ r c)
    (M : Derived R φ W) :
    (G R φ p₁).map ((alphaPullbackBeta R φ c i₁ i h wi si).hom.app M) ≫
        (alpha R φ k₁ r₁ p₁ i₁ w₁).app ((G R φ c).obj M) =
      (alphaPullbackSquareG R φ a p₁ p h wp).hom.app ((J R φ i).obj M) ≫
        (G R φ a).map ((alpha R φ k r p i w).app M) ≫
        (alphaPullbackBeta R φ d k₁ k a wk sk).hom.app ((G R φ r).obj M) ≫
        (J R φ k₁).map ((alphaPullbackSquareG R φ d r₁ r c wr).inv.app M) := by
  have hh := localize_cube_functors
    (Modules R φ W) (Modules R φ Z) (Modules R φ V) (Modules R φ U)
    (Modules R φ W₁) (Modules R φ Z₁) (Modules R φ V₁) (Modules R φ U₁)
    (extension R φ i)
    (pull R φ p)
    (extension R φ k)
    (pull R φ r)
    (extension R φ i₁)
    (pull R φ p₁)
    (extension R φ k₁)
    (pull R φ r₁)
    (pull R φ a)
    (pull R φ h)
    (pull R φ c)
    (pull R φ d)
    (moduleAlpha R φ k r p i w) (moduleAlpha R φ k₁ r₁ p₁ i₁ w₁)
    (moduleBeta R φ c i₁ i h wi si).hom (moduleBeta R φ d k₁ k a wk sk).hom
    (moduleSquareG R φ a p₁ p h wp).hom (moduleSquareG R φ d r₁ r c wr).inv
    (moduleAlpha_baseChange R φ k i r p k₁ i₁ r₁ p₁ a h c d
      w w₁ wk wi wp wr sk si sp sr) M
  simp only [alpha_localized, beta_localized, square_localized, square_inv_localized]
  exact hh

end AlgebraicGeometry.ProEtale.VaryingRing
