/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.LocalMapPairCompatibility
import WeilConjectures.AlgebraicGeometry.OpenCoverTensorDescentComparisonCoherence

/-! # Detecting pairwise compatibility on the base change of the overlap

Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-local-map-pair-overlap-base-change). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Pseudofunctor.DescentData

open LocallyDiscreteOpToCat

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma square_pull
    {C : Type*} [Category* C] {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {X : ι → C} {f : ∀ a, X a ⟶ S}
    {D₁ D₂ : P.DescentData f} (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι)
    {W Z : C} (t : W ⟶ S) (g₁ : W ⟶ X a) (g₂ : W ⟶ X b)
    (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t)
    (h : (P.map g₁.op.toLoc).toFunctor.map (r a) ≫ D₂.hom t g₁ g₂ h₁ h₂ =
      D₁.hom t g₁ g₂ h₁ h₂ ≫ (P.map g₂.op.toLoc).toFunctor.map (r b))
    (l : Z ⟶ W) (t' : Z ⟶ S) (g₁' : Z ⟶ X a) (g₂' : Z ⟶ X b)
    (ht : l ≫ t = t') (hl₁ : l ≫ g₁ = g₁') (hl₂ : l ≫ g₂ = g₂') :
    (P.map g₁'.op.toLoc).toFunctor.map (r a) ≫
        D₂.hom t' g₁' g₂' (by rw [← hl₁, Category.assoc, h₁, ht])
          (by rw [← hl₂, Category.assoc, h₂, ht]) =
      D₁.hom t' g₁' g₂' (by rw [← hl₁, Category.assoc, h₁, ht])
          (by rw [← hl₂, Category.assoc, h₂, ht]) ≫
        (P.map g₂'.op.toLoc).toFunctor.map (r b) := by
  have k := congrArg (fun φ ↦ pullHom (F := P) φ l g₁' g₂' hl₁ hl₂) h
  rw [← D₁.pullHom_hom l t t' ht g₁ g₂ h₁ h₂ g₁' g₂' hl₁ hl₂,
    ← D₂.pullHom_hom l t t' ht g₁ g₂ h₁ h₂ g₁' g₂' hl₁ hl₂]
  dsimp only [pullHom] at k ⊢
  simp only [Functor.map_comp, Category.assoc] at k
  rw [← mapComp'_hom_naturality_assoc, mapComp'_inv_naturality] at k
  simpa only [Category.assoc] using k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma square_pull_iff
    {C : Type*} [Category* C] {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {X : ι → C} {f : ∀ a, X a ⟶ S}
    {D₁ D₂ : P.DescentData f} (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι)
    {W Z : C} (t : W ⟶ S) (g₁ : W ⟶ X a) (g₂ : W ⟶ X b)
    (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t)
    (l : Z ⟶ W) (t' : Z ⟶ S) (g₁' : Z ⟶ X a) (g₂' : Z ⟶ X b)
    (ht : l ≫ t = t') (hl₁ : l ≫ g₁ = g₁') (hl₂ : l ≫ g₂ = g₂') :
    (P.map g₁'.op.toLoc).toFunctor.map (r a) ≫
        D₂.hom t' g₁' g₂' (by rw [← hl₁, Category.assoc, h₁, ht])
          (by rw [← hl₂, Category.assoc, h₂, ht]) =
      D₁.hom t' g₁' g₂' (by rw [← hl₁, Category.assoc, h₁, ht])
          (by rw [← hl₂, Category.assoc, h₂, ht]) ≫
        (P.map g₂'.op.toLoc).toFunctor.map (r b) ↔
    (P.map l.op.toLoc).toFunctor.map
        ((P.map g₁.op.toLoc).toFunctor.map (r a) ≫ D₂.hom t g₁ g₂ h₁ h₂) =
      (P.map l.op.toLoc).toFunctor.map
        (D₁.hom t g₁ g₂ h₁ h₂ ≫ (P.map g₂.op.toLoc).toFunctor.map (r b)) := by
  rw [← D₁.pullHom_hom l t t' ht g₁ g₂ h₁ h₂ g₁' g₂' hl₁ hl₂,
    ← D₂.pullHom_hom l t t' ht g₁ g₂ h₁ h₂ g₁' g₂' hl₁ hl₂]
  dsimp only [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [mapComp'_hom_naturality_assoc, ← mapComp'_inv_naturality]
  simp only [← Category.assoc, cancel_mono]
  simp only [Category.assoc, cancel_epi]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma pairCompatibility_iff_test
    {C : Type*} [Category* C] {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {X : ι → C} {f : ∀ a, X a ⟶ S}
    {D₁ D₂ : P.DescentData f} (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι)
    {W : C} (t : W ⟶ S) (g₁ : W ⟶ X a) (g₂ : W ⟶ X b)
    (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t)
    (hlift : ∀ {Z : C} (t' : Z ⟶ S) (g₁' : Z ⟶ X a) (g₂' : Z ⟶ X b),
      g₁' ≫ f a = t' → g₂' ≫ f b = t' →
      ∃ l : Z ⟶ W, l ≫ t = t' ∧ l ≫ g₁ = g₁' ∧ l ≫ g₂ = g₂') :
    PairCompatibility r a b ↔
      (P.map g₁.op.toLoc).toFunctor.map (r a) ≫ D₂.hom t g₁ g₂ h₁ h₂ =
        D₁.hom t g₁ g₂ h₁ h₂ ≫ (P.map g₂.op.toLoc).toFunctor.map (r b) := by
  refine ⟨fun h ↦ h.comm t g₁ g₂ h₁ h₂, fun h ↦ ⟨?_⟩⟩
  intro Z t' g₁' g₂' h₁' h₂'
  obtain ⟨l, ht, hl₁, hl₂⟩ := hlift t' g₁' g₂' h₁' h₂'
  exact square_pull r a b t g₁ g₂ h₁ h₂ h l t' g₁' g₂' ht hl₁ hl₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma square_conjugate_iff
    {C : Type*} [Category* C] {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {X : ι → C} {f : ∀ a, X a ⟶ S}
    {D₁ D₂ E₁ E₂ : P.DescentData f}
    (e₁ : D₁ ≅ E₁) (e₂ : D₂ ≅ E₂)
    (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι)
    {W : C} (t : W ⟶ S) (g₁ : W ⟶ X a) (g₂ : W ⟶ X b)
    (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t) :
    (P.map g₁.op.toLoc).toFunctor.map (e₁.inv.hom a ≫ r a ≫ e₂.hom.hom a) ≫
        E₂.hom t g₁ g₂ h₁ h₂ =
      E₁.hom t g₁ g₂ h₁ h₂ ≫
        (P.map g₂.op.toLoc).toFunctor.map (e₁.inv.hom b ≫ r b ≫ e₂.hom.hom b) ↔
    (P.map g₁.op.toLoc).toFunctor.map (r a) ≫ D₂.hom t g₁ g₂ h₁ h₂ =
      D₁.hom t g₁ g₂ h₁ h₂ ≫ (P.map g₂.op.toLoc).toFunctor.map (r b) := by
  have hcancel₁ (a : ι) : IsIso (e₁.inv.hom a) :=
    (show E₁.obj a ≅ D₁.obj a from
      ⟨e₁.inv.hom a, e₁.hom.hom a,
        congrArg (fun φ ↦ φ.hom a) e₁.inv_hom_id,
        congrArg (fun φ ↦ φ.hom a) e₁.hom_inv_id⟩).isIso_hom
  have hcancel₂ (a : ι) : IsIso (e₂.hom.hom a) :=
    (show D₂.obj a ≅ E₂.obj a from
      ⟨e₂.hom.hom a, e₂.inv.hom a,
        congrArg (fun φ ↦ φ.hom a) e₂.hom_inv_id,
        congrArg (fun φ ↦ φ.hom a) e₂.inv_hom_id⟩).isIso_hom
  simp only [Functor.map_comp, Category.assoc]
  rw [e₂.hom.comm t g₁ g₂ h₁ h₂, ← e₁.inv.comm_assoc t g₁ g₂ h₁ h₂]
  simp only [← Category.assoc, cancel_mono]
  simp only [Category.assoc, cancel_epi]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma square_pullFunctor_iff
    {C : Type*} [Category* C] {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S S' : C} {X X' : ι → C}
    {f : ∀ a, X a ⟶ S} {f' : ∀ a, X' a ⟶ S'}
    {p : S' ⟶ S} {p' : ∀ a, X' a ⟶ X a}
    (w : ∀ a, p' a ≫ f a = f' a ≫ p)
    {D₁ D₂ : P.DescentData f} (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι)
    {W : C} (t : W ⟶ S') (g₁ : W ⟶ X' a) (g₂ : W ⟶ X' b)
    (h₁ : g₁ ≫ f' a = t) (h₂ : g₂ ≫ f' b = t) :
    let D₁' := (pullFunctor P w).obj D₁
    let D₂' := (pullFunctor P w).obj D₂
    (P.map g₁.op.toLoc).toFunctor.map ((P.map (p' a).op.toLoc).toFunctor.map (r a)) ≫
        D₂'.hom t g₁ g₂ h₁ h₂ =
      D₁'.hom t g₁ g₂ h₁ h₂ ≫
        (P.map g₂.op.toLoc).toFunctor.map ((P.map (p' b).op.toLoc).toFunctor.map (r b)) ↔
    (P.map (g₁ ≫ p' a).op.toLoc).toFunctor.map (r a) ≫
        D₂.hom (t ≫ p) (g₁ ≫ p' a) (g₂ ≫ p' b)
          (by rw [Category.assoc, w, ← Category.assoc, h₁])
          (by rw [Category.assoc, w, ← Category.assoc, h₂]) =
      D₁.hom (t ≫ p) (g₁ ≫ p' a) (g₂ ≫ p' b)
          (by rw [Category.assoc, w, ← Category.assoc, h₁])
          (by rw [Category.assoc, w, ← Category.assoc, h₂]) ≫
        (P.map (g₂ ≫ p' b).op.toLoc).toFunctor.map (r b) := by
  subst t
  dsimp only
  dsimp only [pullFunctor, pullFunctorObj]
  rw [pullFunctorObjHom_eq w D₁ (g₁ ≫ f' a) g₁ g₂ ((g₁ ≫ f' a) ≫ p) (g₁ ≫ p' a) (g₂ ≫ p' b)
      rfl h₂ rfl rfl rfl,
    pullFunctorObjHom_eq w D₂ (g₁ ≫ f' a) g₁ g₂ ((g₁ ≫ f' a) ≫ p) (g₁ ≫ p' a) (g₂ ≫ p' b)
      rfl h₂ rfl rfl rfl]
  simp only [Category.assoc]
  rw [mapComp'_inv_naturality_assoc, ← mapComp'_hom_naturality]
  simp only [← Category.assoc, cancel_mono]
  simp only [Category.assoc, cancel_epi]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma universal_baseChange_square_iff
    {C : Type*} [Category* C] {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S S' : C} {X X' : ι → C}
    {f : ∀ a, X a ⟶ S} {f' : ∀ a, X' a ⟶ S'}
    {p : S' ⟶ S} {p' : ∀ a, X' a ⟶ X a}
    (w : ∀ a, p' a ≫ f a = f' a ≫ p)
    {D₁ D₂ : P.DescentData f} {E₁ E₂ : P.DescentData f'}
    (e₁ : (pullFunctor P w).obj D₁ ≅ E₁)
    (e₂ : (pullFunctor P w).obj D₂ ≅ E₂)
    (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι)
    {W Z : C} (t : W ⟶ S) (g₁ : W ⟶ X a) (g₂ : W ⟶ X b)
    (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t)
    (s : Z ⟶ S') (k₁ : Z ⟶ X' a) (k₂ : Z ⟶ X' b)
    (hk₁ : k₁ ≫ f' a = s) (hk₂ : k₂ ≫ f' b = s)
    (l : Z ⟶ W) (hs : l ≫ t = s ≫ p)
    (hl₁ : l ≫ g₁ = k₁ ≫ p' a) (hl₂ : l ≫ g₂ = k₂ ≫ p' b)
    (hlift : ∀ {Z' : C} (s' : Z' ⟶ S') (k₁' : Z' ⟶ X' a) (k₂' : Z' ⟶ X' b),
      k₁' ≫ f' a = s' → k₂' ≫ f' b = s' →
      ∃ z : Z' ⟶ Z, z ≫ s = s' ∧ z ≫ k₁ = k₁' ∧ z ≫ k₂ = k₂') :
    let r' : ∀ a, E₁.obj a ⟶ E₂.obj a := fun a ↦
      e₁.inv.hom a ≫ (P.map (p' a).op.toLoc).toFunctor.map (r a) ≫ e₂.hom.hom a
    PairCompatibility r' a b ↔
      (P.map l.op.toLoc).toFunctor.map
          ((P.map g₁.op.toLoc).toFunctor.map (r a) ≫ D₂.hom t g₁ g₂ h₁ h₂) =
        (P.map l.op.toLoc).toFunctor.map
          (D₁.hom t g₁ g₂ h₁ h₂ ≫ (P.map g₂.op.toLoc).toFunctor.map (r b)) := by
  dsimp only
  refine (pairCompatibility_iff_test (P := P) (D₁ := E₁) (D₂ := E₂)
    _ a b s k₁ k₂ hk₁ hk₂ hlift).trans ?_
  refine (square_conjugate_iff e₁ e₂
    (fun a ↦ (P.map (p' a).op.toLoc).toFunctor.map (r a)) a b s k₁ k₂ hk₁ hk₂).trans ?_
  refine (square_pullFunctor_iff (P := P) (D₁ := D₁) (D₂ := D₂) w r a b s k₁ k₂ hk₁ hk₂).trans ?_
  exact square_pull_iff (P := P) (D₁ := D₁) (D₂ := D₂) r a b t g₁ g₂ h₁ h₂ l (s ≫ p)
    (k₁ ≫ p' a) (k₂ ≫ p' b) hs hl₁ hl₂

end CategoryTheory.Pseudofunctor.DescentData

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

private lemma native_map_map {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (r : M ⟶ N) :
    (modulesPseudofunctor.map f.op.toLoc).toFunctor.map r =
      (Scheme.Modules.pullback f).map r := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chart hom and inverse maps determine this isomorphism uniquely.
The named characterization theorem supplies only its coherence and uniqueness;
no arbitrary witness of existence is used. -/
private noncomputable def comparisonObj
    {X Y : Scheme.{u}} (U : X.OpenCover.{u}) (q : Y ⟶ X) (M : X.Modules) :
    (Pseudofunctor.DescentData.pullFunctor modulesPseudofunctor
      (f := U.f) (f' := fun x ↦ pullback.fst q (U.f x)) (p := q) (α := id)
      (p' := fun x ↦ U.pullbackHom q x) (fun x ↦ U.pullbackHom_map q x)).obj
      ((modulesPseudofunctor.toDescentData U.f).obj M) ≅
    (modulesPseudofunctor.toDescentData (fun x ↦ pullback.fst q (U.f x))).obj
      ((Scheme.Modules.tensorPullback q).obj M) :=
  Classical.choose (openCoverTensorDescentComparison_existsUnique U q M).exists

private lemma comparisonObj_components
    {X Y : Scheme.{u}} (U : X.OpenCover.{u}) (q : Y ⟶ X) (M : X.Modules) (a : U.I₀) :
    (comparisonObj U q M).hom.hom a =
        (Scheme.Modules.openCoverTensorPullbackComparison q U a).hom.app M ∧
      (comparisonObj U q M).inv.hom a =
        (Scheme.Modules.openCoverTensorPullbackComparison q U a).inv.app M :=
  (Classical.choose_spec (openCoverTensorDescentComparison_existsUnique U q M).exists) a

/-- The overlap defect is the difference of the two sides of the descent square
on the universal overlap. Its source and target are actual pullbacks of modules.
Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-local-map-pair-overlap-base-change). -/
noncomputable def localMapPairOverlapDefect
    {X : Scheme.{u}} (U : X.OpenCover.{u}) (F G : X.Modules)
    (r : ∀ x, (Scheme.Modules.pullback (U.f x)).obj F ⟶
      (Scheme.Modules.pullback (U.f x)).obj G) (a b : U.I₀) :
    (Scheme.Modules.pullback (pullback.fst (U.f a) (U.f b))).obj
        ((Scheme.Modules.pullback (U.f a)).obj F) ⟶
      (Scheme.Modules.pullback (pullback.snd (U.f a) (U.f b))).obj
        ((Scheme.Modules.pullback (U.f b)).obj G) :=
  let Q := modulesPseudofunctor.toDescentData U.f
  let g₁ := pullback.fst (U.f a) (U.f b)
  let g₂ := pullback.snd (U.f a) (U.f b)
  let t := g₁ ≫ U.f a
  let A := (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback (U.f a)).obj F)
  let B := (Scheme.Modules.pullback g₂).obj ((Scheme.Modules.pullback (U.f b)).obj G)
  (show A ⟶ B from (Scheme.Modules.pullback g₁).map (r a) ≫
      (Q.obj G).hom t g₁ g₂ rfl pullback.condition.symm) -
    (show A ⟶ B from (Q.obj F).hom t g₁ g₂ rfl pullback.condition.symm ≫
      (Scheme.Modules.pullback g₂).map (r b))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pairwise compatibility after an arbitrary base change is equivalent to
vanishing of the pulled back, explicitly constructed overlap defect.
Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing;
Mathlib pseudofunctor composition and descent naturality.
(blueprint: lem-pc-local-map-pair-overlap-base-change).

Proof: Let W be the universal overlap of charts a and b, with structural map t.
The pullback W times_X Y is canonically the overlap of the base changed charts.
Pull back the two composites defining the defect to this scheme. Pullback
composition, congruence along the pullback squares, and the unique comparison
between tensor and native pullback identify them, after conjugation by their
invertible source and target comparisons, with the two descent-square composites
for the transported local maps. Naturality moves each local map through the
comparisons, and the pseudofunctor associativity identity identifies the middle
transition maps. Additivity identifies zero of the difference with equality.
If the universal square commutes, pull it back along the unique map from any
universal test into the overlap; descent pullHom naturality gives that test's
square. Conversely evaluate compatibility on the universal overlap and cancel
the invertible comparisons. No compactness, finiteness, affineness or limit is
used. The same argument includes empty overlaps, identity base changes and zero
modules; it uses only canonical universal lifts, never chosen existence data. -/
theorem localMapPairOverlapDefect_baseChange_iff
    {X Y : Scheme.{u}} (U : X.OpenCover.{u}) (F G : X.Modules)
    (r₀ : ∀ x, (Scheme.Modules.pullback (U.f x)).obj F ⟶
      (Scheme.Modules.pullback (U.f x)).obj G) (a b : U.I₀) (q : Y ⟶ X) :
    let W := pullback (U.f a) (U.f b)
    let t : W ⟶ X := pullback.fst (U.f a) (U.f b) ≫ U.f a
    let V := U.pullback₁ q
    let Q := modulesPseudofunctor.toDescentData V.f
    let C := Scheme.Modules.tensorPullback q
    let r : ∀ x, (Q.obj (C.obj F)).obj x ⟶ (Q.obj (C.obj G)).obj x := fun x ↦
      let e := Scheme.Modules.openCoverTensorPullbackComparison q U x
      e.inv.app F ≫ (Scheme.Modules.pullback (U.pullbackHom q x)).map (r₀ x) ≫
        e.hom.app G
    Pseudofunctor.DescentData.PairCompatibility r a b ↔
      (Scheme.Modules.pullback (pullback.fst t q)).map
        (localMapPairOverlapDefect U F G r₀ a b) = 0 := by
  let W := pullback (U.f a) (U.f b)
  let t : W ⟶ X := pullback.fst (U.f a) (U.f b) ≫ U.f a
  let V := U.pullback₁ q
  let Q := modulesPseudofunctor.toDescentData V.f
  let C := Scheme.Modules.tensorPullback q
  let r : ∀ x, (Q.obj (C.obj F)).obj x ⟶ (Q.obj (C.obj G)).obj x := fun x ↦
    let e := Scheme.Modules.openCoverTensorPullbackComparison q U x
    e.inv.app F ≫ (Scheme.Modules.pullback (U.pullbackHom q x)).map (r₀ x) ≫
      e.hom.app G
  change Pseudofunctor.DescentData.PairCompatibility r a b ↔ _
  let π : pullback t q ⟶ W := pullback.fst t q
  let s : pullback t q ⟶ Y := pullback.snd t q
  let ga : pullback t q ⟶ V.X a := pullback.lift s
    (π ≫ pullback.fst (U.f a) (U.f b)) (by
      simpa only [Category.assoc] using (pullback.condition (f := t) (g := q)).symm)
  let gb : pullback t q ⟶ V.X b := pullback.lift s
    (π ≫ pullback.snd (U.f a) (U.f b)) (by
      calc
        s ≫ q = π ≫ t := (pullback.condition (f := t) (g := q)).symm
        _ = (π ≫ pullback.snd (U.f a) (U.f b)) ≫ U.f b := by
          dsimp only [t]
          simpa only [Category.assoc] using congrArg (π ≫ ·)
            (pullback.condition (f := U.f a) (g := U.f b)))
  have ha : ga ≫ V.f a = s := pullback.lift_fst _ _ _
  have hb : gb ≫ V.f b = s := pullback.lift_fst _ _ _
  have hga : ga ≫ U.pullbackHom q a = π ≫ pullback.fst (U.f a) (U.f b) :=
    pullback.lift_snd _ _ _
  have hgb : gb ≫ U.pullbackHom q b = π ≫ pullback.snd (U.f a) (U.f b) :=
    pullback.lift_snd _ _ _
  have hlift {Z : Scheme.{u}} (s' : Z ⟶ Y) (ga' : Z ⟶ V.X a) (gb' : Z ⟶ V.X b)
      (ha' : ga' ≫ V.f a = s') (hb' : gb' ≫ V.f b = s') :
      ∃ l : Z ⟶ pullback t q, l ≫ s = s' ∧ l ≫ ga = ga' ∧ l ≫ gb = gb' := by
    let l₀ : Z ⟶ W := pullback.lift (ga' ≫ U.pullbackHom q a)
      (gb' ≫ U.pullbackHom q b) (by
        rw [Category.assoc, Category.assoc, U.pullbackHom_map, U.pullbackHom_map,
          ← Category.assoc, ← Category.assoc, ha', hb'])
    have hl₀ : l₀ ≫ t = s' ≫ q := by
      dsimp only [t]
      rw [← Category.assoc, pullback.lift_fst, Category.assoc,
        U.pullbackHom_map, ← Category.assoc, ha']
    let l : Z ⟶ pullback t q := pullback.lift l₀ s' hl₀
    have hls : l ≫ s = s' := pullback.lift_snd _ _ _
    have hlπ : l ≫ π = l₀ := pullback.lift_fst _ _ _
    refine ⟨l, hls, ?_, ?_⟩
    · apply pullback.hom_ext
      · change (l ≫ ga) ≫ V.f a = ga' ≫ V.f a
        rw [Category.assoc, ha, hls, ha']
      · change (l ≫ ga) ≫ U.pullbackHom q a = ga' ≫ U.pullbackHom q a
        rw [Category.assoc, hga, ← Category.assoc, hlπ, pullback.lift_fst]
    · apply pullback.hom_ext
      · change (l ≫ gb) ≫ V.f b = gb' ≫ V.f b
        rw [Category.assoc, hb, hls, hb']
      · change (l ≫ gb) ≫ U.pullbackHom q b = gb' ≫ U.pullbackHom q b
        rw [Category.assoc, hgb, ← Category.assoc, hlπ, pullback.lift_snd]
  let eF := comparisonObj U q F
  let eG := comparisonObj U q G
  have hs : s ≫ q = π ≫ t := (pullback.condition (f := t) (g := q)).symm
  have h := Pseudofunctor.DescentData.universal_baseChange_square_iff
    (P := modulesPseudofunctor) (f := U.f)
    (f' := fun x ↦ pullback.fst q (U.f x)) (p := q)
    (p' := fun x ↦ U.pullbackHom q x)
    (D₁ := (modulesPseudofunctor.toDescentData U.f).obj F)
    (D₂ := (modulesPseudofunctor.toDescentData U.f).obj G)
    (fun x ↦ U.pullbackHom_map q x) eF eG r₀ a b t
    (pullback.fst (U.f a) (U.f b)) (pullback.snd (U.f a) (U.f b))
    rfl pullback.condition.symm s ga gb ha hb π hs.symm hga.symm hgb.symm
    (fun s' ga' gb' ha' hb' ↦ hlift s' ga' gb' ha' hb')
  have hr : r = (fun x ↦ eF.inv.hom x ≫
      (Scheme.Modules.pullback (U.pullbackHom q x)).map (r₀ x) ≫ eG.hom.hom x) := by
    funext x
    dsimp only [r]
    rw [(comparisonObj_components U q F x).2, (comparisonObj_components U q G x).1]
  rw [hr]
  refine h.trans ?_
  dsimp only [localMapPairOverlapDefect]
  rw [Functor.map_sub, sub_eq_zero]
  simp only [native_map_map]
  rfl

end AlgebraicGeometry
