/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
public import WeilConjectures.AlgebraicGeometry.TruncatedFiniteSplitEtaleDiagram
public import WeilConjectures.AlgebraicGeometry.DescendSurjective
public import Mathlib.CategoryTheory.Presentable.Directed
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import Mathlib.AlgebraicGeometry.LimitsOver
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
-- This module preserves private proof helpers extracted from the upstream module.
set_option linter.privateModule false

/-!
# Supporting results for `sk-prop-h2`

Supporting results for the blueprint unit `sk-prop-h2` of
`chap-Cohomology-of-torsion-sheaves-on-curves`, grouped from `FiniteHypercoverDescentParts`.
-/

@[expose] public section

/-! ### From `FiniteHypercoverDescentParts` -/
section
/-! # Stage lemmas for finite hypercover descent

Pullback and comparison lemmas for the stages of finite split étale hypercovers, complementing
`WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts`. -/

set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
private theorem pullbackComp_inv_fst {X Y Z : Scheme.{w}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (W : Over Z) :
    ((Over.pullbackComp f g).inv.app W).left ≫ pullback.fst W.hom (f ≫ g) =
      pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g := by
  simp [Over.pullbackComp, Adjunction.comp_counit_app]

private theorem comparison_fst {X Y Z : Scheme.{w}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) (W : Over Z) :
    ((((Over.pullbackComp f g).symm ≪≫
      eqToIso (congrArg (fun t : X ⟶ Z ↦ Over.pullback t) h)).app W).hom).left ≫
        pullback.fst W.hom k =
      pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g := by
  subst k
  simpa using pullbackComp_inv_fst f g W

private theorem finite_etale_cofan_qcqs
    {X : Scheme.{w}} {A : Type*} [Finite A] (V : A → X.Etale)
    (W : X.Etale) (ι : ∀ a, V a ⟶ W) (h : IsColimit (Cofan.mk W ι))
    (hV : ∀ a, CompactSpace (V a).left ∧ QuasiSeparatedSpace (V a).left) :
    CompactSpace W.left ∧ QuasiSeparatedSpace W.left := by
  let F := Scheme.Etale.forget X ⋙ Over.forget X
  have : Small.{w} A := inferInstance
  have : IsZariskiLocalAtSource @Etale := inferInstance
  have : CreatesColimitsOfShape (Discrete A)
      (MorphismProperty.Over.forget @Etale ⊤ X) := inferInstance
  have : PreservesColimitsOfShape (Discrete A) (Scheme.Etale.forget X) := by
    unfold Scheme.Etale.forget
    infer_instance
  have : PreservesColimit (Discrete.functor V) F := by
    dsimp [F]
    infer_instance
  have h' := isColimitCofanMkObjOfIsColimit F V ι h
  let e : W.left ≅ ∐ (fun a ↦ (V a).left) :=
    h'.coconePointUniqueUpToIso (coproductIsCoproduct _)
  obtain ⟨hc, hs, _⟩ := finite_coproduct_lfp_qcqs (fun a ↦ (V a).left) X
    (fun a ↦ (V a).hom)
  have : CompactSpace ↥(∐ (fun a ↦ (V a).left)) := hc (fun a ↦ (hV a).1)
  have : QuasiSeparatedSpace ↥(∐ (fun a ↦ (V a).left)) := hs (fun a ↦ (hV a).2)
  let he := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e).symm
  exact ⟨@Homeomorph.compactSpace _ _ _ _ ‹_› he,
    (quasiSeparatedSpace_congr he).mp ‹_›⟩

private theorem truncated_terms_qcqs {X : Scheme.{w}} {r : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X r)
    (Δ : (SimplexCategory.Truncated r)ᵒᵖ) :
    CompactSpace (U.simplicial.obj Δ).left ∧
      QuasiSeparatedSpace (U.simplicial.obj Δ).left := by
  have hN (n : Fin (r + 1)) :
      CompactSpace (U.N n).left ∧ QuasiSeparatedSpace (U.N n).left := by
    obtain ⟨k, V, ι, ⟨hι⟩, hV⟩ := U.finite_each_degree n
    exact finite_etale_cofan_qcqs V (U.N n) ι hι (fun a ↦ ⟨(hV a).1, (hV a).2.1⟩)
  let A := Σ m : Fin (r + 1),
    {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α}
  exact finite_etale_cofan_qcqs (fun a : A ↦ U.N a.1) (U.simplicial.obj Δ)
    _ (U.splitting Δ) (fun a ↦ hN a.1)

private theorem truncated_finite (r : ℕ) : Finite (SimplexCategory.Truncated r) := by
  apply Finite.of_injective
    (fun Δ : SimplexCategory.Truncated r ↦
      (⟨Δ.obj.len, Nat.lt_succ_of_le Δ.property⟩ : Fin (r + 1)))
  intro a b hab
  apply ObjectProperty.FullSubcategory.ext
  exact SimplexCategory.ext (congrArg Fin.val hab)

private theorem truncated_terms_finitePresentation
    {X : Scheme.{w}} [QuasiSeparatedSpace X] {r : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X r)
    (Δ : (SimplexCategory.Truncated r)ᵒᵖ) :
    LocallyOfFinitePresentation (U.diagram.obj Δ).hom ∧
      QuasiCompact (U.diagram.obj Δ).hom ∧ QuasiSeparated (U.diagram.obj Δ).hom := by
  obtain ⟨hcU, hsU⟩ := truncated_terms_qcqs U Δ
  dsimp [TruncatedFiniteSplitEtaleHypercover.diagram]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_morphism_equalities_lift
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (R : Type*) [Finite R] (i : Iᵒᵖ) (V W : R → Over (D.obj i))
    (hV : ∀ r, LocallyOfFinitePresentation (V r).hom ∧
      QuasiCompact (V r).hom ∧ QuasiSeparated (V r).hom)
    (hW : ∀ r, LocallyOfFinitePresentation (W r).hom ∧
      QuasiCompact (W r).hom ∧ QuasiSeparated (W r).hom)
    (x y : ∀ r, V r ⟶ W r)
    (hxy : ∀ r, (Over.pullback (c.π.app i)).map (x r) =
      (Over.pullback (c.π.app i)).map (y r)) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i), ∀ r,
      (Over.pullback (D.map h)).map (x r) =
        (Over.pullback (D.map h)).map (y r) := by
  classical
  have hex : ∀ r, ∃ (j : Iᵒᵖ) (h : j ⟶ i),
      (Over.pullback (D.map h)).map (x r) =
        (Over.pullback (D.map h)).map (y r) := by
    intro r
    have := (hV r).1
    have := (hV r).2.1
    have := (hV r).2.2
    have := (hW r).1
    have := (hW r).2.1
    have := (hW r).2.2
    have hfst : pullback.fst (V r).hom (c.π.app i) ≫ (x r).left =
        pullback.fst (V r).hom (c.π.app i) ≫ (y r).left := by
      have hh := congrArg
        (fun f ↦ f.left ≫ pullback.fst (W r).hom (c.π.app i)) (hxy r)
      simpa using hh
    obtain ⟨j, h, hh⟩ := Scheme.exists_pullback_fst_comp_eq_of_isLimit
      hc (V r).hom (W r).hom (x r).left (y r).left
      (Over.w (x r)) (Over.w (y r)) hfst
    refine ⟨j, h, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa using hh
    · simp
  choose js fs hfs using hex
  obtain ⟨j, h, g, hg⟩ := IsCofiltered.wideCospan fs
  refine ⟨j, h, fun r ↦ ?_⟩
  let E : Over.pullback (D.map h) ≅
      Over.pullback (D.map (fs r)) ⋙ Over.pullback (D.map (g r)) :=
    eqToIso (congrArg (fun f : j ⟶ i ↦ Over.pullback (D.map f)) (hg r).symm) ≪≫
      eqToIso (congrArg (fun f ↦ Over.pullback f) (D.map_comp (g r) (fs r))) ≪≫
      Over.pullbackComp (D.map (g r)) (D.map (fs r))
  apply (cancel_mono (E.hom.app (W r))).mp
  rw [E.hom.naturality, E.hom.naturality]
  exact congrArg (E.hom.app (V r) ≫ ·)
    (congrArg (fun f ↦ (Over.pullback (D.map (g r))).map f) (hfs r))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_components_lift
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (R : Type*) [Finite R] (i : Iᵒᵖ) (V W : R → Over (D.obj i))
    (hV : ∀ r, LocallyOfFinitePresentation (V r).hom ∧
      QuasiCompact (V r).hom ∧ QuasiSeparated (V r).hom)
    (hW : ∀ r, LocallyOfFinitePresentation (W r).hom ∧
      QuasiCompact (W r).hom ∧ QuasiSeparated (W r).hom)
    (ψ : ∀ r, (Over.pullback (c.π.app i)).obj (V r) ⟶
      (Over.pullback (c.π.app i)).obj (W r)) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i)
      (ψj : ∀ r, (Over.pullback (D.map h)).obj (V r) ⟶
        (Over.pullback (D.map h)).obj (W r)),
      ∀ r, (Over.pullback (c.π.app j)).map (ψj r) ≫
          (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
            eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
              (c.w h))).app (W r)).hom =
        (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
          eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
            (c.w h))).app (V r)).hom ≫ ψ r := by
  classical
  let θ (f : R) := (ψ f).left ≫ pullback.fst (W f).hom (c.π.app i)
  have hθ (f : R) : θ f ≫ (W f).hom =
      pullback.fst (V f).hom (c.π.app i) ≫ (V f).hom := by
    dsimp [θ]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change ((ψ f).left ≫ ((Over.pullback (c.π.app i)).obj (W f)).hom) ≫
      c.π.app i = _
    rw [Over.w, pullback.condition]
    rfl
  have hex (f : R) : ∃ (j : Iᵒᵖ) (h : j ⟶ i)
      (θj : pullback (V f).hom (D.map h) ⟶ (W f).left),
      θj ≫ (W f).hom = pullback.fst (V f).hom (D.map h) ≫ (V f).hom ∧
      pullback.map (V f).hom (c.π.app i) (V f).hom (D.map h)
        (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ θj = θ f := by
    have := (hV f).1
    have := (hV f).2.1
    have := (hV f).2.2
    have := (hW f).1
    have := (hW f).2.1
    have := (hW f).2.2
    exact Scheme.exists_pullback_hom_of_isLimit hc (V f).hom (W f).hom (θ f) (hθ f)
  choose js fs θs hθs hdesc using hex
  obtain ⟨j, h, m, hm⟩ := IsCofiltered.wideCospan fs
  have hmap (f : R) : D.map h = D.map (m f) ≫ D.map (fs f) := by
    rw [← D.map_comp, hm]
  let M (f : R) := pullback.map (V f).hom (D.map h) (V f).hom (D.map (fs f))
    (𝟙 _) (D.map (m f)) (𝟙 _) (by simp) (by simp [hmap f])
  let θj (f : R) := M f ≫ θs f
  have hθj (f : R) : θj f ≫ (W f).hom =
      pullback.fst (V f).hom (D.map h) ≫ (V f).hom := by
    simp [θj, M, hθs f]
  have hj (f : R) : pullback.map (V f).hom (c.π.app i) (V f).hom (D.map h)
      (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ θj f = θ f := by
    have hM : pullback.map (V f).hom (c.π.app i) (V f).hom (D.map h)
        (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ M f =
        pullback.map (V f).hom (c.π.app i) (V f).hom (D.map (fs f))
          (𝟙 _) (c.π.app (js f)) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext
      · simp [M]
      · simp [M, c.w (m f)]
    dsimp [θj]
    rw [← Category.assoc, hM]
    exact hdesc f
  let ej (f : R) : (Over.pullback (D.map h)).obj (V f) ⟶
      (Over.pullback (D.map h)).obj (W f) :=
    Over.homMk (pullback.lift (θj f) (pullback.snd (V f).hom (D.map h))
      ((hθj f).trans pullback.condition)) (by simp)
  let K := (Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))
  have hK (W : Over (D.obj i)) :
      (K.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) =
        pullback.fst (pullback.snd W.hom (D.map h)) (c.π.app j) ≫
          pullback.fst W.hom (D.map h) :=
    by
      simpa only [K, Iso.app_hom] using
        comparison_fst (c.π.app j) (D.map h) (c.π.app i) (c.w h) W
  have he (f : R) : (Over.pullback (c.π.app j)).map (ej f) ≫ K.hom.app (W f) =
      K.hom.app (V f) ≫ ψ f := by
    have hM : (K.hom.app (V f)).left ≫
        pullback.map (V f).hom (c.π.app i) (V f).hom (D.map h)
          (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) =
        pullback.fst (pullback.snd (V f).hom (D.map h)) (c.π.app j) := by
      apply pullback.hom_ext
      · simpa using hK (V f)
      · simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
        change (K.hom.app (V f)).left ≫
          ((Over.pullback (c.π.app i)).obj (V f)).hom ≫ c.π.app j = _
        rw [← Category.assoc, Over.w]
        exact pullback.condition.symm
    ext1
    apply pullback.hom_ext
    · change (((Over.pullback (c.π.app j)).map (ej f)).left ≫
          (K.hom.app (W f)).left) ≫ pullback.fst (W f).hom (c.π.app i) =
        ((K.hom.app (V f)).left ≫ (ψ f).left) ≫
          pullback.fst (W f).hom (c.π.app i)
      rw [Category.assoc, hK (W f)]
      have hmapp : ((Over.pullback (c.π.app j)).map (ej f)).left ≫
          pullback.fst (pullback.snd (W f).hom (D.map h)) (c.π.app j) =
          pullback.fst (pullback.snd (V f).hom (D.map h)) (c.π.app j) ≫ (ej f).left := by
        simp
      rw [← Category.assoc, hmapp, Category.assoc]
      rw [show (ej f).left ≫ pullback.fst (W f).hom (D.map h) = θj f by simp [ej]]
      rw [← hM, Category.assoc, hj]
      simp only [θ, Category.assoc]
    · exact (Over.w (((Over.pullback (c.π.app j)).map (ej f)) ≫ K.hom.app (W f))).trans
        (Over.w (K.hom.app (V f) ≫ ψ f)).symm
  exact ⟨j, h, ej, he⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_isIso_stage
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (R : Type*) [Finite R] (i : Iᵒᵖ)
    (V W : R → Over (D.obj i))
    (hV : ∀ r, LocallyOfFinitePresentation (V r).hom ∧
      QuasiCompact (V r).hom ∧ QuasiSeparated (V r).hom)
    (hW : ∀ r, LocallyOfFinitePresentation (W r).hom ∧
      QuasiCompact (W r).hom ∧ QuasiSeparated (W r).hom)
    (f : ∀ r, V r ⟶ W r)
    (hf : ∀ r, IsIso ((Over.pullback (c.π.app i)).map (f r))) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i), ∀ r,
      IsIso ((Over.pullback (D.map h)).map (f r)) := by
  classical
  let L := Over.pullback (c.π.app i)
  let e (r : R) : L.obj (V r) ≅ L.obj (W r) := @asIso _ _ _ _ (L.map (f r)) (hf r)
  obtain ⟨j, h, g, hg⟩ := finite_components_lift D c hc R i W V hW hV (fun r ↦ (e r).inv)
  let P := Over.pullback (D.map h)
  let Q := Over.pullback (c.π.app j)
  let K : P ⋙ Q ≅ L := (Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
    eqToIso (congrArg (fun k ↦ Over.pullback k) (c.w h))
  have hg' (r : R) : Q.map (g r) ≫ K.hom.app (V r) =
      K.hom.app (W r) ≫ (e r).inv := hg r
  let V' (r : R) := P.obj (V r)
  let W' (r : R) := P.obj (W r)
  let f' (r : R) : V' r ⟶ W' r := P.map (f r)
  have hV' (r : R) : LocallyOfFinitePresentation (V' r).hom ∧
      QuasiCompact (V' r).hom ∧ QuasiSeparated (V' r).hom := by
    have := (hV r).1
    have := (hV r).2.1
    have := (hV r).2.2
    change LocallyOfFinitePresentation (pullback.snd (V r).hom (D.map h)) ∧
      QuasiCompact (pullback.snd (V r).hom (D.map h)) ∧
      QuasiSeparated (pullback.snd (V r).hom (D.map h))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hW' (r : R) : LocallyOfFinitePresentation (W' r).hom ∧
      QuasiCompact (W' r).hom ∧ QuasiSeparated (W' r).hom := by
    have := (hW r).1
    have := (hW r).2.1
    have := (hW r).2.2
    change LocallyOfFinitePresentation (pullback.snd (W r).hom (D.map h)) ∧
      QuasiCompact (pullback.snd (W r).hom (D.map h)) ∧
      QuasiSeparated (pullback.snd (W r).hom (D.map h))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let A : R ⊕ R → Over (D.obj j) := Sum.elim V' W'
  let x : ∀ a, A a ⟶ A a := fun a ↦ match a with
    | .inl r => f' r ≫ g r
    | .inr r => g r ≫ f' r
  have hA (a : R ⊕ R) : LocallyOfFinitePresentation (A a).hom ∧
      QuasiCompact (A a).hom ∧ QuasiSeparated (A a).hom := by
    cases a with
    | inl r => exact hV' r
    | inr r => exact hW' r
  have hx (a : R ⊕ R) : Q.map (x a) = Q.map (𝟙 (A a)) := by
    cases a with
    | inl r =>
      apply (cancel_mono (K.hom.app (V r))).mp
      change Q.map (f' r ≫ g r) ≫ K.hom.app (V r) = _
      calc
        _ = Q.map (f' r) ≫ (Q.map (g r) ≫ K.hom.app (V r)) := by
          rw [Q.map_comp, Category.assoc]
        _ = (Q.map (f' r) ≫ K.hom.app (W r)) ≫ (e r).inv := by
          rw [hg', Category.assoc]
        _ = (K.hom.app (V r) ≫ L.map (f r)) ≫ (e r).inv :=
          congrArg (· ≫ (e r).inv) (K.hom.naturality (f r))
        _ = _ := by simp [e, Category.assoc]
    | inr r =>
      apply (cancel_mono (K.hom.app (W r))).mp
      change Q.map (g r ≫ f' r) ≫ K.hom.app (W r) = _
      calc
        _ = Q.map (g r) ≫ (Q.map (f' r) ≫ K.hom.app (W r)) := by
          rw [Q.map_comp, Category.assoc]
        _ = (Q.map (g r) ≫ K.hom.app (V r)) ≫ L.map (f r) :=
          (congrArg (Q.map (g r) ≫ ·) (K.hom.naturality (f r))).trans
            (Category.assoc _ _ _).symm
        _ = _ := by rw [hg']; simp [e, Category.assoc]
  obtain ⟨k, l, hl⟩ := finite_morphism_equalities_lift D c hc _ j A A hA hA x
    (fun a ↦ 𝟙 (A a)) hx
  let B := Over.pullback (D.map l)
  refine ⟨k, l ≫ h, fun r ↦ ?_⟩
  let t : B.obj (V' r) ≅ B.obj (W' r) :=
    { hom := B.map (f' r)
      inv := B.map (g r)
      hom_inv_id := by
        have hh := hl (.inl r)
        change B.map (f' r ≫ g r) = B.map (𝟙 (V' r)) at hh
        simpa only [B.map_comp, B.map_id] using hh
      inv_hom_id := by
        have hh := hl (.inr r)
        change B.map (g r ≫ f' r) = B.map (𝟙 (W' r)) at hh
        simpa only [B.map_comp, B.map_id] using hh }
  let E : Over.pullback (D.map (l ≫ h)) ≅ P ⋙ B :=
    eqToIso (congrArg (fun a ↦ Over.pullback a) (D.map_comp l h)) ≪≫
      Over.pullbackComp _ _
  have he : (Over.pullback (D.map (l ≫ h))).map (f r) =
      E.hom.app (V r) ≫ (P ⋙ B).map (f r) ≫ E.inv.app (W r) := by
    rw [← E.hom.naturality_assoc, E.hom_inv_id_app, Category.comp_id]
  have : IsIso ((P ⋙ B).map (f r)) := t.isIso_hom
  rw [he]
  infer_instance

private theorem over_pullback_isPullback {S T : Scheme.{w}} (g : T ⟶ S)
    {V W : Over S} (f : V ⟶ W) :
    IsPullback (pullback.fst V.hom g) ((Over.pullback g).map f).left f.left
      (pullback.fst W.hom g) := by
  apply IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback W.hom g)
  simpa using IsPullback.of_hasPullback V.hom g

private theorem over_pullback_surjective {S T : Scheme.{w}} (g : T ⟶ S)
    {V W : Over S} (f : V ⟶ W) (hf : Surjective f.left) :
    Surjective ((Over.pullback g).map f).left :=
  MorphismProperty.of_isPullback (over_pullback_isPullback g f) hf

private theorem surjective_map_of_iso {S T : Scheme.{w}}
    (F G : Over S ⥤ Over T) (e : F ≅ G) {V W : Over S} (f : V ⟶ W)
    (hf : Surjective (G.map f).left) : Surjective (F.map f).left := by
  have he : F.map f = e.hom.app V ≫ G.map f ≫ e.inv.app W := by
    rw [← e.hom.naturality_assoc, e.hom_inv_id_app]
    simp
  have := hf
  rw [he]
  change Surjective ((e.hom.app V).left ≫ (G.map f).left ≫ (e.inv.app W).left)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem filtered_surjective_stage
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : Iᵒᵖ)
    (V W : Over (D.obj i)) (f : V ⟶ W)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    [LocallyOfFinitePresentation f.left]
    (hf : Surjective ((Over.pullback (c.π.app i)).map f).left) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i), Surjective ((Over.pullback (D.map h)).map f).left := by
  obtain ⟨A, hA, hdir, hne, F, hF⟩ := IsFiltered.exists_directed I
  let := hA
  let := hdir
  let := hne
  let := hF
  obtain ⟨a, ⟨s⟩⟩ := (F.final_iff_of_isFiltered.mp inferInstance).1 i.unop
  let h : F.op.obj (op a) ⟶ i := s.op
  let D' := F.op ⋙ D
  let c' := c.whisker F.op
  have : ∀ {a b : Aᵒᵖ} (t : a ⟶ b), IsAffineHom (D'.map t) :=
    fun t ↦ inferInstanceAs (IsAffineHom (D.map (F.op.map t)))
  have : ∀ a : Aᵒᵖ, CompactSpace (D'.obj a) :=
    fun a ↦ inferInstanceAs (CompactSpace (D.obj (F.op.obj a)))
  have : ∀ a : Aᵒᵖ, QuasiSeparatedSpace (D'.obj a) :=
    fun a ↦ inferInstanceAs (QuasiSeparatedSpace (D.obj (F.op.obj a)))
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv F.op c).symm hc
  let V' := (Over.pullback (D.map h)).obj V
  let W' := (Over.pullback (D.map h)).obj W
  let f' : V' ⟶ W' := (Over.pullback (D.map h)).map f
  have : QuasiCompact V.hom := inferInstance
  have : QuasiSeparated V.hom := inferInstance
  have : QuasiCompact W.hom := inferInstance
  have : QuasiSeparated W.hom := inferInstance
  have : QuasiCompact V'.hom := by
    change QuasiCompact (pullback.snd V.hom (D.map h))
    infer_instance
  have : QuasiSeparated V'.hom := by
    change QuasiSeparated (pullback.snd V.hom (D.map h))
    infer_instance
  have : QuasiCompact W'.hom := by
    change QuasiCompact (pullback.snd W.hom (D.map h))
    infer_instance
  have : QuasiSeparated W'.hom := by
    change QuasiSeparated (pullback.snd W.hom (D.map h))
    infer_instance
  have : CompactSpace V'.left :=
    QuasiCompact.compactSpace_of_compactSpace V'.hom
  have : QuasiSeparatedSpace V'.left := quasiSeparatedSpace_of_quasiSeparated V'.hom
  have : CompactSpace W'.left :=
    QuasiCompact.compactSpace_of_compactSpace W'.hom
  have : QuasiSeparatedSpace W'.left := quasiSeparatedSpace_of_quasiSeparated W'.hom
  have : LocallyOfFinitePresentation f'.left := by
    exact MorphismProperty.of_isPullback (over_pullback_isPullback (D.map h) f)
      inferInstance
  let E : Over.pullback (D.map h) ⋙ Over.pullback (c.π.app (F.op.obj (op a))) ≅
      Over.pullback (c.π.app i) :=
    (Over.pullbackComp _ _).symm ≪≫
      eqToIso (congrArg (fun k ↦ Over.pullback k) (c.w h))
  have hf' : Surjective ((Over.pullback (c'.π.app (op a))).map f').left :=
    surjective_map_of_iso _ _ E f hf
  obtain ⟨b, hab, hb⟩ := exists_surjective_of_isLimit D' c' hc' a V' W' f' hf'
  let t : F.op.obj (op b) ⟶ F.op.obj (op a) := F.op.map (homOfLE hab).op
  let K : Over.pullback (D.map (t ≫ h)) ≅
      Over.pullback (D.map h) ⋙ Over.pullback (D.map t) :=
    eqToIso (congrArg (fun k ↦ Over.pullback k) (D.map_comp t h)) ≪≫
      Over.pullbackComp _ _
  exact ⟨F.op.obj (op b), t ≫ h, surjective_map_of_iso _ _ K f hb⟩
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_surjective_stage
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : Iᵒᵖ)
    (R : Type*) [Finite R] (V W : R → Over (D.obj i)) (f : ∀ r, V r ⟶ W r)
    (hV : ∀ r, CompactSpace (V r).left ∧ QuasiSeparatedSpace (V r).left)
    (hW : ∀ r, CompactSpace (W r).left ∧ QuasiSeparatedSpace (W r).left)
    (hfp : ∀ r, LocallyOfFinitePresentation (f r).left)
    (hf : ∀ r, Surjective ((Over.pullback (c.π.app i)).map (f r)).left) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i), ∀ r,
      Surjective ((Over.pullback (D.map h)).map (f r)).left := by
  classical
  have hex (r : R) : ∃ (j : Iᵒᵖ) (h : j ⟶ i),
      Surjective ((Over.pullback (D.map h)).map (f r)).left := by
    have := (hV r).1
    have := (hV r).2
    have := (hW r).1
    have := (hW r).2
    have := hfp r
    exact filtered_surjective_stage D c hc i (V r) (W r) (f r) (hf r)
  choose js hs hsurj using hex
  obtain ⟨j, h, m, hm⟩ := IsCofiltered.wideCospan hs
  refine ⟨j, h, fun r ↦ ?_⟩
  let E : Over.pullback (D.map h) ≅
      Over.pullback (D.map (hs r)) ⋙ Over.pullback (D.map (m r)) :=
    eqToIso (congrArg (fun k ↦ Over.pullback (D.map k)) (hm r).symm) ≪≫
      eqToIso (congrArg (fun k ↦ Over.pullback k) (D.map_comp (m r) (hs r))) ≪≫
        Over.pullbackComp _ _
  exact surjective_map_of_iso _ _ E (f r)
    (over_pullback_surjective _ _ (hsurj r))

private theorem raw_terms_qcqs {X : Scheme.{w}} {r : ℕ}
    (U : TruncatedFiniteSplitEtaleDiagram X r)
    (Δ : (SimplexCategory.Truncated r)ᵒᵖ) :
    CompactSpace (U.simplicial.obj Δ).left ∧
      QuasiSeparatedSpace (U.simplicial.obj Δ).left := by
  have hN (n : Fin (r + 1)) :
      CompactSpace (U.N n).left ∧ QuasiSeparatedSpace (U.N n).left := by
    obtain ⟨k, V, ι, ⟨hι⟩, hV⟩ := U.finite_each_degree n
    exact finite_etale_cofan_qcqs V (U.N n) ι hι (fun a ↦ ⟨(hV a).1, (hV a).2.1⟩)
  let A := Σ m : Fin (r + 1),
    {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α}
  exact finite_etale_cofan_qcqs (fun a : A ↦ U.N a.1) (U.simplicial.obj Δ)
    _ (U.splitting Δ) (fun a ↦ hN a.1)

private theorem over_surjective_of_iso_square {X : Scheme.{w}}
    {A B C E : Over X} (f : A ⟶ B) (g : C ⟶ E) (a : A ≅ C) (b : B ≅ E)
    (h : f ≫ b.hom = a.hom ≫ g) (hg : Surjective g.left) : Surjective f.left := by
  have hf : f = a.hom ≫ g ≫ b.inv := (Iso.eq_comp_inv b).mpr h
  have := hg
  rw [hf]
  change Surjective (a.hom.left ≫ g.left ≫ b.inv.left)
  have : IsIso a.hom.left := ((Over.forget X).mapIso a).isIso_hom
  have : IsIso b.inv.left := ((Over.forget X).mapIso b).isIso_inv
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem matching_map_surjective_of_iso
    {X : Scheme.{w}} {r : ℕ} (U : TruncatedFiniteSplitEtaleDiagram X r)
    (V : TruncatedFiniteSplitEtaleHypercover X r) (e : U.diagram ≅ V.diagram)
    (n : Fin (r + 1)) : Surjective (U.matchingMap n).left := by
  dsimp only [TruncatedFiniteSplitEtaleDiagram.diagram,
    TruncatedFiniteSplitEtaleHypercover.diagram] at e
  let F := Scheme.Etale.forget X
  let A := F.obj (U.matching n)
  let B := F.obj (V.matching n)
  have extU (T : Over X) (f g : T ⟶ A)
      (h : ∀ (Δ : SimplexCategory.Truncated r) (hΔ : Δ.obj.len < n.val)
        (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
        f ≫ F.map (U.projection n Δ hΔ θ) = g ≫ F.map (U.projection n Δ hΔ θ)) :
      f = g := by
    obtain ⟨q, hq, huniq⟩ := U.matching_universal n T
      (fun Δ hΔ θ ↦ f ≫ F.map (U.projection n Δ hΔ θ)) (by
        intro Δ Δ' hΔ hΔ' α θ
        change (f ≫ F.map (U.projection n Δ hΔ θ)) ≫
            F.map (U.simplicial.map α.op) = _
        erw [Category.assoc,
          ← F.map_comp (U.projection n Δ hΔ θ) (U.simplicial.map α.op),
          U.projection_naturality])
    exact (huniq f (fun _ _ _ ↦ rfl)).trans (huniq g (fun Δ hΔ θ ↦ (h Δ hΔ θ).symm)).symm
  have extV (T : Over X) (f g : T ⟶ B)
      (h : ∀ (Δ : SimplexCategory.Truncated r) (hΔ : Δ.obj.len < n.val)
        (θ : Δ.obj ⟶ SimplexCategory.mk n.val),
        f ≫ F.map (V.projection n Δ hΔ θ) = g ≫ F.map (V.projection n Δ hΔ θ)) :
      f = g := by
    obtain ⟨q, hq, huniq⟩ := V.matching_universal n T
      (fun Δ hΔ θ ↦ f ≫ F.map (V.projection n Δ hΔ θ)) (by
        intro Δ Δ' hΔ hΔ' α θ
        change (f ≫ F.map (V.projection n Δ hΔ θ)) ≫
            F.map (V.simplicial.map α.op) = _
        erw [Category.assoc,
          ← F.map_comp (V.projection n Δ hΔ θ) (V.simplicial.map α.op),
          V.projection_naturality])
    exact (huniq f (fun _ _ _ ↦ rfl)).trans (huniq g (fun Δ hΔ θ ↦ (h Δ hΔ θ).symm)).symm
  obtain ⟨a, ha, _⟩ := V.matching_universal n A
    (fun Δ hΔ θ ↦ F.map (U.projection n Δ hΔ θ) ≫ e.hom.app (op Δ)) (by
      intro Δ Δ' hΔ hΔ' α θ
      change (F.map (U.projection n Δ hΔ θ) ≫ e.hom.app (op Δ)) ≫
        V.diagram.map α.op = _
      erw [Category.assoc, ← e.hom.naturality α.op, ← Category.assoc]
      change (F.map (U.projection n Δ hΔ θ) ≫ F.map (U.simplicial.map α.op)) ≫ _ = _
      erw [← F.map_comp (U.projection n Δ hΔ θ) (U.simplicial.map α.op),
        U.projection_naturality])
  obtain ⟨b, hb, _⟩ := U.matching_universal n B
    (fun Δ hΔ θ ↦ F.map (V.projection n Δ hΔ θ) ≫ e.inv.app (op Δ)) (by
      intro Δ Δ' hΔ hΔ' α θ
      change (F.map (V.projection n Δ hΔ θ) ≫ e.inv.app (op Δ)) ≫
        U.diagram.map α.op = _
      erw [Category.assoc, ← e.inv.naturality α.op, ← Category.assoc]
      change (F.map (V.projection n Δ hΔ θ) ≫ F.map (V.simplicial.map α.op)) ≫ _ = _
      erw [← F.map_comp (V.projection n Δ hΔ θ) (V.simplicial.map α.op),
        V.projection_naturality])
  have hab : a ≫ b = 𝟙 A := by
    apply extU
    intro Δ hΔ θ
    change (a ≫ b) ≫ F.map (U.projection n Δ hΔ θ) =
      𝟙 A ≫ F.map (U.projection n Δ hΔ θ)
    erw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
      e.hom_inv_id_app, Category.comp_id]
  have hba : b ≫ a = 𝟙 B := by
    apply extV
    intro Δ hΔ θ
    change (b ≫ a) ≫ F.map (V.projection n Δ hΔ θ) =
      𝟙 B ≫ F.map (V.projection n Δ hΔ θ)
    erw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
      e.inv_hom_id_app, Category.comp_id]
  let m : A ≅ B := ⟨a, b, hab, hba⟩
  have hm : F.map (U.matchingMap n) ≫ m.hom =
      e.hom.app (op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩) ≫
        F.map (V.matchingMap n) := by
    apply extV
    intro Δ hΔ θ
    change (F.map (U.matchingMap n) ≫ a) ≫ F.map (V.projection n Δ hΔ θ) = _
    erw [Category.assoc, ha, ← Category.assoc,
      ← F.map_comp (U.matchingMap n) (U.projection n Δ hΔ θ), U.matchingMap_projection]
    erw [Category.assoc,
      ← F.map_comp (V.matchingMap n) (V.projection n Δ hΔ θ), V.matchingMap_projection]
    exact e.hom.naturality _
  exact over_surjective_of_iso_square (F.map (U.matchingMap n))
    (F.map (V.matchingMap n))
    (e.app (op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩)) m hm
    (V.matching_cover n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_hypercover_descent_of_diagram_models
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (r : ℕ) (U : TruncatedFiniteSplitEtaleHypercover c.pt r)
    (hmodels : ∃ (i : Iᵒᵖ) (V : TruncatedFiniteSplitEtaleDiagram (D.obj i) r),
      V.IsBaseChange (c.π.app i) U) :
    ∃ (i : Iᵒᵖ) (Ui : TruncatedFiniteSplitEtaleHypercover (D.obj i) r),
      Ui.IsBaseChange (c.π.app i) U ∧
        ∀ (j : Iᵒᵖ) (h : j ⟶ i) (n : Fin (r + 1)),
          Surjective ((Over.pullback (D.map h)).map
            ((Scheme.Etale.forget (D.obj i)).map (Ui.matchingMap n))).left := by
  obtain ⟨i, V, hV⟩ := hmodels
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  have : QuasiSeparatedSpace c.pt :=
    @quasiSeparatedSpace_of_quasiSeparated c.pt (D.obj i) (c.π.app i)
      inferInstance inferInstance
  have hcov (n : Fin (r + 1)) : Surjective ((Over.pullback (c.π.app i)).map
      ((Scheme.Etale.forget (D.obj i)).map (V.matchingMap n))).left :=
    matching_map_surjective_of_iso
      (@TruncatedFiniteSplitEtaleDiagram.pullback c.pt (D.obj i) inferInstance
        inferInstance inferInstance r V (c.π.app i)) U hV.choose n
  let A (n : Fin (r + 1)) := (Scheme.Etale.forget (D.obj i)).obj
    (V.simplicial.obj (op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩))
  let B (n : Fin (r + 1)) := (Scheme.Etale.forget (D.obj i)).obj (V.matching n)
  let f (n : Fin (r + 1)) : A n ⟶ B n :=
    (Scheme.Etale.forget (D.obj i)).map (V.matchingMap n)
  have hA (n : Fin (r + 1)) :
      CompactSpace (A n).left ∧ QuasiSeparatedSpace (A n).left :=
    raw_terms_qcqs V _
  have hB (n : Fin (r + 1)) :
      CompactSpace (B n).left ∧ QuasiSeparatedSpace (B n).left := V.matching_qcqs n
  have hfp (n : Fin (r + 1)) : LocallyOfFinitePresentation (f n).left := by
    change LocallyOfFinitePresentation (V.matchingMap n).left
    infer_instance
  obtain ⟨j, h, hj⟩ := finite_surjective_stage D c hc i _ A B f hA hB hfp hcov
  have hcover (n : Fin (r + 1)) :
      Surjective ((V.pullback (D.map h)).matchingMap n).left := hj n
  let W := (V.pullback (D.map h)).toHypercover hcover
  have hbase : W.IsBaseChange (c.π.app j) U :=
    V.isBaseChange_pullback U (c.π.app j) (D.map h) (c.π.app i) (c.w h) hV hcover
  have hpersist : ∀ (k : Iᵒᵖ) (t : k ⟶ j) (n : Fin (r + 1)),
      Surjective ((Over.pullback (D.map t)).map
        ((Scheme.Etale.forget (D.obj j)).map (W.matchingMap n))).left := by
    intro k t n
    exact over_pullback_surjective (D.map t)
      ((Scheme.Etale.forget (D.obj j)).map (W.matchingMap n)) (hcover n)
  exact ⟨j, W, hbase, hpersist⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_etale_diagram_descent
    {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (J : Type*) [SmallCategory J] [Finite J] [∀ a b : J, Finite (a ⟶ b)]
    (F : J ⥤ c.pt.Etale)
    (hF : ∀ a, CompactSpace (F.obj a).left ∧ QuasiSeparatedSpace (F.obj a).left) :
    ∃ (i : Iᵒᵖ) (G : J ⥤ (D.obj i).Etale),
      (∀ a, CompactSpace (G.obj a).left ∧ QuasiSeparatedSpace (G.obj a).left) ∧
        Nonempty ((G ⋙ Scheme.Etale.forget (D.obj i)) ⋙ Over.pullback (c.π.app i) ≅
          F ⋙ Scheme.Etale.forget c.pt) := by
  classical
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := Iᵒᵖ)
  have : IsAffineHom (c.π.app i₀) := isAffineHom_π_app D c hc i₀
  have : QuasiSeparatedSpace c.pt :=
    @quasiSeparatedSpace_of_quasiSeparated c.pt (D.obj i₀) (c.π.app i₀)
      inferInstance inferInstance
  let R := J ⊕ (Σ a b d : J, (a ⟶ b) × (b ⟶ d))
  let s : R → Paths J := fun r ↦ r.elim id (fun x ↦ x.1)
  let t : R → Paths J := fun r ↦ r.elim id (fun x ↦ x.2.2.1)
  let p : ∀ r, s r ⟶ t r := fun r ↦ match r with
    | .inl a => (Paths.of J).map (𝟙 a)
    | .inr ⟨a, b, d, f, g⟩ => (Paths.of J).map f ≫ (Paths.of J).map g
  let q : ∀ r, s r ⟶ t r := fun r ↦ match r with
    | .inl a => Quiver.Path.nil
    | .inr ⟨a, b, d, f, g⟩ => (Paths.of J).map (f ≫ g)
  let F' := pathComposition J ⋙ F ⋙ Scheme.Etale.forget c.pt
  have hF' (a : Paths J) : Etale (F'.obj a).hom ∧
      LocallyOfFinitePresentation (F'.obj a).hom ∧ QuasiCompact (F'.obj a).hom ∧
      QuasiSeparated (F'.obj a).hom := by
    have := (hF a).1
    have := (hF a).2
    change Etale (F.obj a).hom ∧ LocallyOfFinitePresentation (F.obj a).hom ∧
      QuasiCompact (F.obj a).hom ∧ QuasiSeparated (F.obj a).hom
    exact ⟨inferInstance, inferInstance,
      @quasiCompact_of_compactSpace (F.obj a).left c.pt (F.obj a).hom
        (hF a).1 inferInstance,
      @QuasiSeparated.of_quasiSeparatedSpace (F.obj a).left c.pt (F.obj a).hom
        (hF a).2⟩
  have hR (r : R) : F'.map (p r) = F'.map (q r) := by
    cases r with
    | inl a => simp [F', p, q, pathComposition, s, CategoryTheory.Functor.map_id]
    | inr x => rcases x with ⟨a, b, d, f, g⟩; simp [F', p, q, pathComposition, s]
  obtain ⟨i, G, α, hG, hGR, _⟩ :=
    (etale_finite_data_descent D c hc).2.2.2.1 J R s t p q F' hF' hR
  let H : J ⥤ (D.obj i).Etale :=
    { obj := fun a ↦ MorphismProperty.Over.mk ⊤ (G.obj a).hom (hG a).1
      map := fun {a b} f ↦ MorphismProperty.Over.homMk
        (G.map ((Paths.of J).map f)).left (Over.w (G.map ((Paths.of J).map f)))
      map_id := by
        intro a
        apply MorphismProperty.Over.Hom.ext
        have h := hGR (Sum.inl a)
        change (G.map ((Paths.of J).map (𝟙 a))).left = 𝟙 _
        have hnil : G.map (q (Sum.inl a)) = 𝟙 (G.obj a) := G.map_id a
        exact congrArg Over.Hom.left (h.trans hnil)
      map_comp := by
        intro a b d f g
        apply MorphismProperty.Over.Hom.ext
        have h := hGR (Sum.inr ⟨a, b, d, f, g⟩)
        change (G.map ((Paths.of J).map (f ≫ g))).left =
          (G.map ((Paths.of J).map f)).left ≫ (G.map ((Paths.of J).map g)).left
        simpa [p, q] using (congrArg Over.Hom.left h).symm }
  refine ⟨i, H, fun a ↦ ?_, ⟨?_⟩⟩
  · have := (hG a).2.2.1
    have := (hG a).2.2.2
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (G.obj a).hom,
      quasiSeparatedSpace_of_quasiSeparated (G.obj a).hom⟩
  · refine NatIso.ofComponents (fun a ↦ α.app a) (fun {a b} f ↦ ?_)
    change (Over.pullback (c.π.app i)).map (G.map ((Paths.of J).map f)) ≫
      α.hom.app b = α.hom.app a ≫ (Scheme.Etale.forget c.pt).map (F.map f)
    have hα := α.hom.naturality ((Paths.of J).map f)
    dsimp only [F', Functor.comp_map, Functor.comp_obj, Paths.of, pathComposition] at hα ⊢
    simpa only [composePath_toPath] using hα

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem filtered_finite_etale_diagram_descent
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (J : Type*) [SmallCategory J] [Finite J] [∀ a b : J, Finite (a ⟶ b)]
    (H : J ⥤ c.pt.Etale)
    (hH : ∀ a, CompactSpace (H.obj a).left ∧ QuasiSeparatedSpace (H.obj a).left) :
    ∃ (i : Iᵒᵖ) (G : J ⥤ (D.obj i).Etale),
      (∀ a, CompactSpace (G.obj a).left ∧ QuasiSeparatedSpace (G.obj a).left) ∧
        Nonempty ((G ⋙ Scheme.Etale.forget (D.obj i)) ⋙ Over.pullback (c.π.app i) ≅
          H ⋙ Scheme.Etale.forget c.pt) := by
  obtain ⟨A, hA, hdir, hne, F, hF⟩ := IsFiltered.exists_directed I
  let := hA
  let := hdir
  let := hne
  let := hF
  let D' := F.op ⋙ D
  let c' := c.whisker F.op
  have : ∀ {a b : Aᵒᵖ} (t : a ⟶ b), IsAffineHom (D'.map t) :=
    fun t ↦ inferInstanceAs (IsAffineHom (D.map (F.op.map t)))
  have : ∀ a : Aᵒᵖ, CompactSpace (D'.obj a) :=
    fun a ↦ inferInstanceAs (CompactSpace (D.obj (F.op.obj a)))
  have : ∀ a : Aᵒᵖ, QuasiSeparatedSpace (D'.obj a) :=
    fun a ↦ inferInstanceAs (QuasiSeparatedSpace (D.obj (F.op.obj a)))
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv F.op c).symm hc
  obtain ⟨a, G, hG, ⟨e⟩⟩ := finite_etale_diagram_descent D' c' hc' J H hH
  exact ⟨F.op.obj a, G, hG, ⟨e⟩⟩

private def degree {r : ℕ} (n : Fin (r + 1)) : (SimplexCategory.Truncated r)ᵒᵖ :=
  op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cofan_iso_colimit {C : Type*} [Category C] {A : Type*}
    {V W : A → C} {P Q : C} (u : ∀ a, V a ⟶ P) (v : ∀ a, W a ⟶ Q)
    (a : ∀ x, V x ≅ W x) (e : P ≅ Q)
    (h : ∀ x, u x ≫ e.hom = (a x).hom ≫ v x)
    (hc : IsColimit (Cofan.mk Q v)) : Nonempty (IsColimit (Cofan.mk P u)) := by
  exact ⟨(IsColimit.equivOfNatIsoOfIso (Discrete.natIso (fun x ↦ a x.as))
    (Cofan.mk P u) (Cofan.mk Q v) (Cofan.ext e (fun x ↦ by
      change ((a x).inv ≫ u x) ≫ e.hom = v x
      rw [Category.assoc, h]
      simp))).symm hc⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etale_pullback_forget_isIso {X Y : Scheme.{w}} (f : X ⟶ Y)
    {V W : Y.Etale} (g : V ⟶ W) (h : IsIso (f.Etale.map g)) :
    IsIso ((Over.pullback f).map ((Scheme.Etale.forget Y).map g)) := by
  let := h
  exact inferInstanceAs (IsIso ((Scheme.Etale.forget X).map (f.Etale.map g)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etale_pullback_reflect_isIso {X Y : Scheme.{w}} (f : X ⟶ Y)
    {V W : Y.Etale} (g : V ⟶ W)
    (h : IsIso ((Over.pullback f).map ((Scheme.Etale.forget Y).map g))) :
    IsIso (f.Etale.map g) := by
  have : IsIso ((Scheme.Etale.forget X).map (f.Etale.map g)) := h
  exact isIso_of_reflects_iso _ (Scheme.Etale.forget X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_cofan_stage
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (R : Type*) [Finite R] (i : Iᵒᵖ)
    (A : R → Type*) [∀ r, Finite (A r)]
    (V : ∀ r, A r → (D.obj i).Etale) (W : R → (D.obj i).Etale)
    (ι : ∀ r a, V r a ⟶ W r)
    (hV : ∀ r a, CompactSpace (V r a).left ∧ QuasiSeparatedSpace (V r a).left)
    (hW : ∀ r, CompactSpace (W r).left ∧ QuasiSeparatedSpace (W r).left)
    (hl : ∀ r, Nonempty (IsColimit (Cofan.mk ((c.π.app i).Etale.obj (W r))
      (fun a ↦ (c.π.app i).Etale.map (ι r a))))) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i), ∀ r,
      Nonempty (IsColimit (Cofan.mk ((D.map h).Etale.obj (W r))
        (fun a ↦ (D.map h).Etale.map (ι r a)))) := by
  classical
  have : IsZariskiLocalAtSource @Etale.{w} := inferInstance
  have : ∀ r, CreatesColimitsOfShape (Discrete (A r))
      (MorphismProperty.Over.forget @Etale.{w} ⊤ (D.obj i)) := fun r ↦ inferInstance
  have (r : R) : HasCoproduct (V r) := by
    have : CreatesColimitsOfShape (Discrete (A r)) (Scheme.Etale.forget (D.obj i)) := by
      unfold Scheme.Etale.forget
      infer_instance
    exact hasColimit_of_created (Discrete.functor (V r)) (Scheme.Etale.forget (D.obj i))
  let P (r : R) : (D.obj i).Etale := ∐ (V r)
  let q (r : R) : P r ⟶ W r := Sigma.desc (ι r)
  have hP (r : R) : CompactSpace (P r).left ∧ QuasiSeparatedSpace (P r).left :=
    finite_etale_cofan_qcqs (V r) (P r) (Sigma.ι (V r))
      (coproductIsCoproduct (V r)) (hV r)
  let F := Scheme.Etale.forget (D.obj i)
  have hFP (r : R) : LocallyOfFinitePresentation (F.obj (P r)).hom ∧
      QuasiCompact (F.obj (P r)).hom ∧ QuasiSeparated (F.obj (P r)).hom := by
    refine ⟨?_,
      @quasiCompact_of_compactSpace (P r).left (D.obj i) (P r).hom (hP r).1 inferInstance,
      @QuasiSeparated.of_quasiSeparatedSpace (P r).left (D.obj i) (P r).hom (hP r).2⟩
    change LocallyOfFinitePresentation (P r).hom
    infer_instance
  have hFW (r : R) : LocallyOfFinitePresentation (F.obj (W r)).hom ∧
      QuasiCompact (F.obj (W r)).hom ∧ QuasiSeparated (F.obj (W r)).hom := by
    refine ⟨?_,
      @quasiCompact_of_compactSpace (W r).left (D.obj i) (W r).hom (hW r).1 inferInstance,
      @QuasiSeparated.of_quasiSeparatedSpace (W r).left (D.obj i) (W r).hom (hW r).2⟩
    change LocallyOfFinitePresentation (W r).hom
    infer_instance
  have hq (r : R) : IsIso ((Over.pullback (c.π.app i)).map (F.map (q r))) := by
    let B := (c.π.app i).Etale
    let hp := TruncatedFiniteSplitEtaleDiagram.finite_etale_cofan_pullback
      (c.π.app i) (V r) (P r) (Sigma.ι (V r)) (coproductIsCoproduct (V r))
    have hdesc : hp.desc (Cofan.mk (B.obj (W r)) (fun a ↦ B.map (ι r a))) =
        B.map (q r) := by
      apply hp.hom_ext
      intro a
      calc
        _ = B.map (ι r a.as) := hp.fac _ a
        _ = B.map (Sigma.ι (V r) a.as) ≫ B.map (q r) :=
          (congrArg B.map (Sigma.ι_comp_desc (ι r) a.as)).symm.trans
            (B.map_comp (Sigma.ι (V r) a.as) (q r))
    have hiso : IsIso (B.map (q r)) := by
      rw [← hdesc]
      exact (hp.nonempty_isColimit_iff_isIso_desc).mp (hl r)
    exact etale_pullback_forget_isIso (c.π.app i) (q r) hiso
  obtain ⟨j, h, hh⟩ := finite_isIso_stage D c hc R i
    (fun r ↦ F.obj (P r)) (fun r ↦ F.obj (W r)) hFP hFW
    (fun r ↦ F.map (q r)) hq
  refine ⟨j, h, fun r ↦ ?_⟩
  let B := (D.map h).Etale
  have : IsIso (B.map (q r)) := etale_pullback_reflect_isIso (D.map h) (q r) (hh r)
  let hp := TruncatedFiniteSplitEtaleDiagram.finite_etale_cofan_pullback
    (D.map h) (V r) (P r) (Sigma.ι (V r)) (coproductIsCoproduct (V r))
  apply (hp.nonempty_isColimit_iff_isIso_desc).mpr
  have hdesc : hp.desc (Cofan.mk (B.obj (W r)) (fun a ↦ B.map (ι r a))) =
      B.map (q r) := by
    apply hp.hom_ext
    intro a
    calc
      _ = B.map (ι r a.as) := hp.fac _ a
      _ = B.map (Sigma.ι (V r) a.as) ≫ B.map (q r) :=
        (congrArg B.map (Sigma.ι_comp_desc (ι r) a.as)).symm.trans
          (B.map_comp (Sigma.ι (V r) a.as) (q r))
  rw [hdesc]
  infer_instance

private inductive FiniteSplitIndex (r : ℕ)
  | summand : Fin (r + 1) → FiniteSplitIndex r
  | simplex : (SimplexCategory.Truncated r)ᵒᵖ → FiniteSplitIndex r
namespace FiniteSplitIndex
private def Hom {r : ℕ} : FiniteSplitIndex r → FiniteSplitIndex r → Type
  | .summand n, .summand m => PLift (n = m)
  | .summand n, .simplex Δ => degree n ⟶ Δ
  | .simplex _, .summand _ => PEmpty
  | .simplex Δ, .simplex Γ => Δ ⟶ Γ
private def id {r : ℕ} : (a : FiniteSplitIndex r) → Hom a a
  | .summand _ => ⟨rfl⟩
  | .simplex _ => 𝟙 _
private def comp {r : ℕ} : {a b c : FiniteSplitIndex r} → Hom a b → Hom b c → Hom a c
  | .summand _, .summand _, .summand _, f, g => ⟨f.down.trans g.down⟩
  | .summand _, .summand _, .simplex _, f, g => by obtain ⟨rfl⟩ := f; exact g
  | .summand _, .simplex _, .simplex _, f, g => f ≫ g
  | .simplex _, .simplex _, .simplex _, f, g => f ≫ g
private instance category {r : ℕ} : SmallCategory (FiniteSplitIndex r) where
  Hom := Hom
  id := id
  comp := comp
  id_comp := by
    intro a b f
    cases a <;> cases b <;> simp only [Hom, id, comp, Category.id_comp] at *
    · rfl
    · exact PEmpty.elim f
  comp_id := by
    intro a b f
    cases a <;> cases b <;> simp only [Hom, id, comp, Category.comp_id] at *
    · rfl
    · exact PEmpty.elim f
  assoc := by
    intro a b c d f g h
    cases a <;> cases b <;> cases c <;> cases d <;>
      dsimp only [Hom, comp] at * <;> try contradiction
    all_goals first
      | rfl
      | (obtain ⟨rfl⟩ := f; rfl)
private def inclusion (r : ℕ) : (SimplexCategory.Truncated r)ᵒᵖ ⥤ FiniteSplitIndex r where
  obj := simplex
  map := fun f ↦ f
private def arrow {r : ℕ} (n : Fin (r + 1)) : summand n ⟶ simplex (degree n) := (𝟙 (degree n))
private def diagram {X : Scheme.{w}} {r : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X r) : FiniteSplitIndex r ⥤ X.Etale where
  obj a := match a with
    | .summand n => U.N n
    | .simplex Δ => U.simplicial.obj Δ
  map {a b} f := match a, b, f with
    | .summand _, .summand _, h => eqToHom (congrArg U.N h.down)
    | .summand n, .simplex _, θ => U.inclusion n ≫ U.simplicial.map θ
    | .simplex _, .simplex _, α => U.simplicial.map α
  map_id := by
    intro a
    cases a with
    | summand n => rfl
    | simplex Δ =>
      change U.simplicial.map (𝟙 Δ) = 𝟙 _
      exact U.simplicial.map_id Δ
  map_comp := by
    intro a b c f g
    cases a <;> cases b <;> cases c <;>
      dsimp only [category, Hom, comp] at * <;> try contradiction
    · obtain ⟨rfl⟩ := f
      obtain ⟨rfl⟩ := g
      simp
    · obtain ⟨rfl⟩ := f
      rfl
    · erw [U.simplicial.map_comp, Category.assoc]
    · exact U.simplicial.map_comp f g
end FiniteSplitIndex

private theorem finiteSplitIndex_finite (r : ℕ) : Finite (FiniteSplitIndex r) := by
  let : Finite (SimplexCategory.Truncated r) := truncated_finite r
  let : Finite (SimplexCategory.Truncated r)ᵒᵖ :=
    Finite.of_injective Opposite.unop (fun _ _ h ↦ congrArg Opposite.op h)
  apply Finite.of_surjective
    (Sum.elim FiniteSplitIndex.summand FiniteSplitIndex.simplex)
  intro a
  cases a with
  | summand n => exact ⟨Sum.inl n, rfl⟩
  | simplex Δ => exact ⟨Sum.inr Δ, rfl⟩
private theorem truncated_op_hom_finite {r : ℕ}
    (a b : (SimplexCategory.Truncated r)ᵒᵖ) : Finite (a ⟶ b) := by
  apply Finite.of_injective (fun f : a ⟶ b ↦ f.unop.hom)
  intro f g h
  apply Quiver.Hom.unop_inj
  exact SimplexCategory.Truncated.Hom.ext _ _
    (congrArg SimplexCategory.Hom.toOrderHom h)
private theorem finiteSplitIndex_hom_finite {r : ℕ} (a b : FiniteSplitIndex r) :
    Finite (a ⟶ b) := by
  cases a with
  | summand n =>
    cases b with
    | summand m => exact inferInstanceAs (Finite (PLift (n = m)))
    | simplex Δ => exact truncated_op_hom_finite _ _
  | simplex Δ =>
    cases b with
    | summand m => exact inferInstanceAs (Finite PEmpty)
    | simplex Γ => exact truncated_op_hom_finite _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem preliminary_split_model
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (r : ℕ)
    (U : TruncatedFiniteSplitEtaleHypercover c.pt r) :
    ∃ (i : Iᵒᵖ) (S : SimplicialObject.Truncated (D.obj i).Etale r)
      (N : Fin (r + 1) → (D.obj i).Etale)
      (ι : ∀ n, N n ⟶ S.obj (degree n))
      (e : (S ⋙ Scheme.Etale.forget (D.obj i)) ⋙ Over.pullback (c.π.app i) ≅ U.diagram)
      (a : ∀ n, (Over.pullback (c.π.app i)).obj
        ((Scheme.Etale.forget (D.obj i)).obj (N n)) ≅
          (Scheme.Etale.forget c.pt).obj (U.N n)),
      (∀ Δ, CompactSpace (S.obj Δ).left ∧ QuasiSeparatedSpace (S.obj Δ).left) ∧
      (∀ n, CompactSpace (N n).left ∧ QuasiSeparatedSpace (N n).left) ∧
      ∀ n, (Over.pullback (c.π.app i)).map
          ((Scheme.Etale.forget (D.obj i)).map (ι n)) ≫ e.hom.app (degree n) =
        (a n).hom ≫ (Scheme.Etale.forget c.pt).map (U.inclusion n) := by
  let : Finite (FiniteSplitIndex r) := finiteSplitIndex_finite r
  have : ∀ a b : FiniteSplitIndex r, Finite (a ⟶ b) := finiteSplitIndex_hom_finite
  have hN (n : Fin (r + 1)) :
      CompactSpace (U.N n).left ∧ QuasiSeparatedSpace (U.N n).left := by
    obtain ⟨k, V, ι, ⟨hι⟩, hV⟩ := U.finite_each_degree n
    exact finite_etale_cofan_qcqs V (U.N n) ι hι (fun a ↦ ⟨(hV a).1, (hV a).2.1⟩)
  have hF (a : FiniteSplitIndex r) :
      CompactSpace ((FiniteSplitIndex.diagram U).obj a).left ∧
        QuasiSeparatedSpace ((FiniteSplitIndex.diagram U).obj a).left := by
    cases a with
    | summand n => exact hN n
    | simplex Δ => exact truncated_terms_qcqs U Δ
  obtain ⟨i, H, hH, ⟨e⟩⟩ := filtered_finite_etale_diagram_descent D c hc
    (FiniteSplitIndex r) (FiniteSplitIndex.diagram U) hF
  let S := FiniteSplitIndex.inclusion r ⋙ H
  let N (n : Fin (r + 1)) := H.obj (FiniteSplitIndex.summand n)
  let ι (n : Fin (r + 1)) : N n ⟶ S.obj (degree n) :=
    H.map (FiniteSplitIndex.arrow n)
  let eS : (S ⋙ Scheme.Etale.forget (D.obj i)) ⋙ Over.pullback (c.π.app i) ≅
      U.diagram := Functor.isoWhiskerLeft (FiniteSplitIndex.inclusion r) e
  refine ⟨i, S, N, ι, eS, fun n ↦ e.app (FiniteSplitIndex.summand n),
    fun Δ ↦ hH (FiniteSplitIndex.simplex Δ), fun n ↦ hH (FiniteSplitIndex.summand n), ?_⟩
  intro n
  have h0 : (FiniteSplitIndex.diagram U).map (FiniteSplitIndex.arrow n) =
      U.inclusion n := by
    change U.inclusion n ≫ U.simplicial.map (𝟙 (degree n)) = U.inclusion n
    erw [U.simplicial.map_id, Category.comp_id]
  have he := e.hom.naturality (FiniteSplitIndex.arrow n)
  simp only [Functor.comp_map, h0] at he
  change (Over.pullback (c.π.app i)).map
      ((Scheme.Etale.forget (D.obj i)).map (ι n)) ≫ eS.hom.app (degree n) =
    (e.app (FiniteSplitIndex.summand n)).hom ≫
      (Scheme.Etale.forget c.pt).map (U.inclusion n) at he
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etale_pullback_qcqs {X Y : Scheme.{w}}
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) (V : Y.Etale)
    (hV : CompactSpace V.left ∧ QuasiSeparatedSpace V.left) :
    CompactSpace (f.Etale.obj V).left ∧ QuasiSeparatedSpace (f.Etale.obj V).left := by
  have : QuasiCompact V.hom :=
    @quasiCompact_of_compactSpace V.left Y V.hom hV.1 inferInstance
  have : QuasiSeparated V.hom :=
    @QuasiSeparated.of_quasiSeparatedSpace V.left Y V.hom hV.2
  have : QuasiCompact (f.Etale.obj V).hom := by
    change QuasiCompact (pullback.snd V.hom f)
    infer_instance
  have : QuasiSeparated (f.Etale.obj V).hom := by
    change QuasiSeparated (pullback.snd V.hom f)
    infer_instance
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (Y := X) (f.Etale.obj V).hom,
    quasiSeparatedSpace_of_quasiSeparated (Y := X) (f.Etale.obj V).hom⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem split_diagram_model
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (r : ℕ)
    (U : TruncatedFiniteSplitEtaleHypercover c.pt r) :
    ∃ (i : Iᵒᵖ) (V : TruncatedFiniteSplitEtaleDiagram (D.obj i) r),
      V.IsBaseChange (c.π.app i) U := by
  classical
  obtain ⟨i, S, N, ι, e, a, hS, hN, hι⟩ := preliminary_split_model D c hc r U
  let A (Δ : (SimplexCategory.Truncated r)ᵒᵖ) :=
    Σ m : Fin (r + 1), {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α}
  let θ (Δ : (SimplexCategory.Truncated r)ᵒᵖ) (x : A Δ) : degree x.1 ⟶ Δ :=
    (SimplexCategory.Truncated.Hom.tr x.2.val Δ.unop.property
      (Nat.le_of_lt_succ x.1.isLt)).op
  let legs (Δ : (SimplexCategory.Truncated r)ᵒᵖ) (x : A Δ) :=
    ι x.1 ≫ S.map (θ Δ x)
  have hl (Δ : (SimplexCategory.Truncated r)ᵒᵖ) :
      Nonempty (IsColimit (Cofan.mk ((c.π.app i).Etale.obj (S.obj Δ))
        (fun x : A Δ ↦ (c.π.app i).Etale.map (legs Δ x)))) := by
    let F := Scheme.Etale.forget c.pt
    let ea (x : A Δ) : (c.π.app i).Etale.obj (N x.1) ≅ U.N x.1 :=
      F.preimageIso (a x.1)
    let ee : (c.π.app i).Etale.obj (S.obj Δ) ≅ U.simplicial.obj Δ :=
      F.preimageIso (e.app Δ)
    apply cofan_iso_colimit _ _ ea ee _ (U.splitting Δ)
    intro x
    apply F.map_injective
    simp only [F.map_comp, ee, ea, Functor.preimageIso_hom, F.map_preimage]
    change (Over.pullback (c.π.app i)).map
        ((Scheme.Etale.forget (D.obj i)).map (ι x.1 ≫ S.map (θ Δ x))) ≫
        e.hom.app Δ = (a x.1).hom ≫
          F.map (U.inclusion x.1 ≫ U.simplicial.map (θ Δ x))
    erw [(Scheme.Etale.forget (D.obj i)).map_comp,
      (Over.pullback (c.π.app i)).map_comp, Category.assoc,
      e.hom.naturality (θ Δ x), ← Category.assoc, hι, Category.assoc]
  let : Finite (SimplexCategory.Truncated r) := truncated_finite r
  let : Finite (SimplexCategory.Truncated r)ᵒᵖ :=
    Finite.of_injective Opposite.unop (fun _ _ h ↦ congrArg Opposite.op h)
  obtain ⟨j, h, hj⟩ := finite_cofan_stage D c hc
    ((SimplexCategory.Truncated r)ᵒᵖ) i A
    (fun Δ x ↦ N x.1) S.obj legs (fun Δ x ↦ hN x.1) hS hl
  let B := (D.map h).Etale
  let S' := S ⋙ B
  let T : TruncatedFiniteSplitEtaleSplitting (D.obj j) r S' :=
    { N := fun n ↦ B.obj (N n)
      inclusion := fun n ↦ B.map (ι n)
      splitting := fun Δ ↦ by
        have hh := hj Δ
        change Nonempty (IsColimit (Cofan.mk (B.obj (S.obj Δ))
          (fun x : A Δ ↦ B.map (ι x.1 ≫ S.map (θ Δ x))))) at hh
        simp only [B.map_comp] at hh
        exact hh.some
      N_qcqs := fun n ↦ etale_pullback_qcqs (D.map h) (N n) (hN n) }
  have hS' (Δ : (SimplexCategory.Truncated r)ᵒᵖ) :
      CompactSpace (S'.obj Δ).left ∧ QuasiSeparatedSpace (S'.obj Δ).left :=
    etale_pullback_qcqs (D.map h) (S.obj Δ) (hS Δ)
  obtain ⟨M⟩ := exists_truncated_etale_matching_data (D.obj j) S' hS'
  let V := TruncatedFiniteSplitEtaleDiagram.ofSplitting S' T M
  let K := (Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))
  let e' := Functor.isoWhiskerLeft (S ⋙ Scheme.Etale.forget (D.obj i)) K ≪≫ e
  refine ⟨j, V, e', fun n ↦ ⟨K.app ((Scheme.Etale.forget (D.obj i)).obj (N n)) ≪≫
    a n, ?_⟩⟩
  change (Over.pullback (c.π.app j)).map
      ((Over.pullback (D.map h)).map ((Scheme.Etale.forget (D.obj i)).map (ι n))) ≫
      (K.hom.app ((Scheme.Etale.forget (D.obj i)).obj (S.obj (degree n))) ≫
        e.hom.app (degree n)) =
    (K.hom.app ((Scheme.Etale.forget (D.obj i)).obj (N n)) ≫ (a n).hom) ≫
      (Scheme.Etale.forget c.pt).map (U.inclusion n)
  calc
    _ = (K.hom.app _ ≫ (Over.pullback (c.π.app i)).map
          ((Scheme.Etale.forget (D.obj i)).map (ι n))) ≫ e.hom.app (degree n) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ e.hom.app (degree n))
          (K.hom.naturality ((Scheme.Etale.forget (D.obj i)).map (ι n))))
    _ = _ := by
      simpa only [Category.assoc] using congrArg (K.hom.app _ ≫ ·) (hι n)

end AlgebraicGeometry
end
