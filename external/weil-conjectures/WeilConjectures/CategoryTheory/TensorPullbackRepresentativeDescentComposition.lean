/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Composition law of descended tensor comparisons

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0D6D
(auxiliary; not a blueprint node).

Derived tensor comparisons descended from representatives, as in
`tensorComparisonDescent`, inherit the composition law of their representative
comparisons, provided the derived compositor is the descent of the representative
compositor.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {KY : Type u₁} {KX : Type u₂} {KZ : Type u₃} {DY : Type u₄} {DX : Type u₅}
  {DZ : Type u₆} [Category.{v₁} KY] [Category.{v₂} KX] [Category.{v₃} KZ]
  [Category.{v₄} DY] [Category.{v₅} DX] [Category.{v₆} DZ]

/-- The pointwise composition law of descended tensor comparisons on representatives.
For representatives `X`, `Y` and `A = qY X`, `B = qY Y`, the following square commutes:
```
  Lhf(A ⊗ B) ──────── σhf ────────→ Lhf A ⊗ Lhf B
      │ μ                                 │ μ ⊗ μ
      ↓                                   ↓
  Lh Lf(A ⊗ B) ─ Lh σf → Lh(Lf A ⊗ Lf B) ─ σh → Lh Lf A ⊗ Lh Lf B
```
Source: Stacks 07A4 and 0D6D (auxiliary; not a blueprint node).
Proof: precompose with the source tensor identification and postcompose with the
invertible comparisons of the two inputs. Both sides then become the localization of
the representative composite, by the descent squares, naturality of the derived
compositor, of `σ_h` and of `ε_h`, and the representative composition law. -/
theorem tensorComparisonDescent_comp_app
    (qY : KY ⥤ DY) (qX : KX ⥤ DX) (qZ : KZ ⥤ DZ)
    (Ff : KY ⥤ KX) (Fh : KX ⥤ KZ) (Fhf : KY ⥤ KZ)
    (Lf : DY ⥤ DX) (Lh : DX ⥤ DZ) (Lhf : DY ⥤ DZ)
    (εf : qY ⋙ Lf ⟶ Ff ⋙ qX) (εh : qX ⋙ Lh ⟶ Fh ⋙ qZ) (εhf : qY ⋙ Lhf ⟶ Fhf ⋙ qZ)
    (PY : ObjectProperty KY) (PX : ObjectProperty KX) (PZ : ObjectProperty KZ)
    (hFf : ∀ X, PY X → PX (Ff.obj X)) (hFh : ∀ X, PX X → PZ (Fh.obj X))
    (hFhf : ∀ X, PY X → PZ (Fhf.obj X))
    (tY : KY × KY ⥤ KY) (tX : KX × KX ⥤ KX) (tZ : KZ × KZ ⥤ KZ)
    (TY : DY × DY ⥤ DY) (TX : DX × DX ⥤ DX) (TZ : DZ × DZ ⥤ DZ)
    (rY : (PY.ι.prod PY.ι) ⋙ tY ⋙ qY ≅ ((PY.ι ⋙ qY).prod (PY.ι ⋙ qY)) ⋙ TY)
    (rX : (PX.ι.prod PX.ι) ⋙ tX ⋙ qX ≅ ((PX.ι ⋙ qX).prod (PX.ι ⋙ qX)) ⋙ TX)
    (rZ : (PZ.ι.prod PZ.ι) ⋙ tZ ⋙ qZ ≅ ((PZ.ι ⋙ qZ).prod (PZ.ι ⋙ qZ)) ⋙ TZ)
    (bf : tY ⋙ Ff ≅ (Ff.prod Ff) ⋙ tX) (bh : tX ⋙ Fh ≅ (Fh.prod Fh) ⋙ tZ)
    (bhf : tY ⋙ Fhf ≅ (Fhf.prod Fhf) ⋙ tZ)
    (σf : TY ⋙ Lf ≅ (Lf.prod Lf) ⋙ TX) (σh : TX ⋙ Lh ≅ (Lh.prod Lh) ⋙ TZ)
    (σhf : TY ⋙ Lhf ≅ (Lhf.prod Lhf) ⋙ TZ)
    (hσf : ∀ (X Y : KY) (hx : PY X) (hy : PY Y),
      Lf.map (rY.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ σf.hom.app (qY.obj X, qY.obj Y) ≫
          TX.map (Prod.mkHom (εf.app X) (εf.app Y)) =
        εf.app (tY.obj (X, Y)) ≫ qX.map (bf.hom.app (X, Y)) ≫
          rX.hom.app (⟨Ff.obj X, hFf X hx⟩, ⟨Ff.obj Y, hFf Y hy⟩))
    (hσh : ∀ (X Y : KX) (hx : PX X) (hy : PX Y),
      Lh.map (rX.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ σh.hom.app (qX.obj X, qX.obj Y) ≫
          TZ.map (Prod.mkHom (εh.app X) (εh.app Y)) =
        εh.app (tX.obj (X, Y)) ≫ qZ.map (bh.hom.app (X, Y)) ≫
          rZ.hom.app (⟨Fh.obj X, hFh X hx⟩, ⟨Fh.obj Y, hFh Y hy⟩))
    (hσhf : ∀ (X Y : KY) (hx : PY X) (hy : PY Y),
      Lhf.map (rY.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ σhf.hom.app (qY.obj X, qY.obj Y) ≫
          TZ.map (Prod.mkHom (εhf.app X) (εhf.app Y)) =
        εhf.app (tY.obj (X, Y)) ≫ qZ.map (bhf.hom.app (X, Y)) ≫
          rZ.hom.app (⟨Fhf.obj X, hFhf X hx⟩, ⟨Fhf.obj Y, hFhf Y hy⟩))
    (m : Fhf ≅ Ff ⋙ Fh) (μ : Lhf ≅ Lf ⋙ Lh)
    (hμ : ∀ X : KY, εhf.app X ≫ qZ.map (m.hom.app X) =
      μ.hom.app (qY.obj X) ≫ Lh.map (εf.app X) ≫ εh.app (Ff.obj X))
    (hm : ∀ X Y : KY, bhf.hom.app (X, Y) ≫ tZ.map (Prod.mkHom (m.hom.app X) (m.hom.app Y)) =
      m.hom.app (tY.obj (X, Y)) ≫ Fh.map (bf.hom.app (X, Y)) ≫
        bh.hom.app (Ff.obj X, Ff.obj Y))
    (hεf : ∀ X, PY X → IsIso (εf.app X)) (hεh : ∀ X, PX X → IsIso (εh.app X))
    (X Y : KY) (hx : PY X) (hy : PY Y) :
    σhf.hom.app (qY.obj X, qY.obj Y) ≫
        TZ.map (Prod.mkHom (μ.hom.app (qY.obj X)) (μ.hom.app (qY.obj Y))) =
      μ.hom.app (TY.obj (qY.obj X, qY.obj Y)) ≫ Lh.map (σf.hom.app (qY.obj X, qY.obj Y)) ≫
        σh.hom.app (Lf.obj (qY.obj X), Lf.obj (qY.obj Y)) := by
  have := hεf X hx
  have := hεf Y hy
  have := hεh _ (hFf X hx)
  have := hεh _ (hFf Y hy)
  let w : ∀ V : KY, (Lf ⋙ Lh).obj (qY.obj V) ⟶ qZ.obj (Fh.obj (Ff.obj V)) :=
    fun V ↦ Lh.map (εf.app V) ≫ εh.app (Ff.obj V)
  have : IsIso (TZ.map (Prod.mkHom (w X) (w Y))) := by
    have : IsIso (Prod.mkHom (w X) (w Y)) :=
      ⟨⟨Prod.mkHom (inv (w X)) (inv (w Y)), by ext <;> simp, by ext <;> simp⟩⟩
    infer_instance
  apply (cancel_epi (Lhf.map (rY.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)))).1
  apply (cancel_mono (TZ.map (Prod.mkHom (w X) (w Y)))).1
  -- the common normal form
  let NF := μ.hom.app (qY.obj (tY.obj (X, Y))) ≫ Lh.map (εf.app (tY.obj (X, Y))) ≫
    εh.app (Ff.obj (tY.obj (X, Y))) ≫ qZ.map (Fh.map (bf.hom.app (X, Y))) ≫
    qZ.map (bh.hom.app (Ff.obj X, Ff.obj Y)) ≫
    rZ.hom.app (⟨Fh.obj (Ff.obj X), hFh _ (hFf X hx)⟩, ⟨Fh.obj (Ff.obj Y), hFh _ (hFf Y hy)⟩)
  have hl : Lhf.map (rY.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ (σhf.hom.app (qY.obj X, qY.obj Y) ≫
      TZ.map (Prod.mkHom (μ.hom.app (qY.obj X)) (μ.hom.app (qY.obj Y)))) ≫
      TZ.map (Prod.mkHom (w X) (w Y)) = NF := by
    have e₁ : TZ.map (Prod.mkHom (μ.hom.app (qY.obj X)) (μ.hom.app (qY.obj Y))) ≫
        TZ.map (Prod.mkHom (w X) (w Y)) =
      TZ.map (Prod.mkHom (εhf.app X) (εhf.app Y)) ≫
        TZ.map (Prod.mkHom (qZ.map (m.hom.app X)) (qZ.map (m.hom.app Y))) := by
      simp only [← TZ.map_comp, prod_comp, w, hμ]
    have e₂ := rZ.hom.naturality
      (X := (⟨Fhf.obj X, hFhf X hx⟩, ⟨Fhf.obj Y, hFhf Y hy⟩))
      (Y := (⟨Fh.obj (Ff.obj X), hFh _ (hFf X hx)⟩, ⟨Fh.obj (Ff.obj Y), hFh _ (hFf Y hy)⟩))
      (Prod.mkHom (ObjectProperty.homMk (m.hom.app X)) (ObjectProperty.homMk (m.hom.app Y)))
    dsimp only [Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
      ObjectProperty.homMk_hom] at e₂
    have e₃ := hμ (tY.obj (X, Y))
    rw [Category.assoc, e₁, reassoc_of% (hσhf X Y hx hy), ← e₂, ← qZ.map_comp_assoc, hm]
    simp only [NF, Functor.map_comp, Category.assoc, reassoc_of% e₃]
  have hr : Lhf.map (rY.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ (μ.hom.app (TY.obj (qY.obj X, qY.obj Y)) ≫
      Lh.map (σf.hom.app (qY.obj X, qY.obj Y)) ≫
        σh.hom.app (Lf.obj (qY.obj X), Lf.obj (qY.obj Y))) ≫
      TZ.map (Prod.mkHom (w X) (w Y)) = NF := by
    have e₁ := μ.hom.naturality (rY.hom.app (⟨X, hx⟩, ⟨Y, hy⟩))
    have e₂ := σh.hom.naturality (Prod.mkHom (εf.app X) (εf.app Y))
    have e₃ : σh.hom.app (qX.obj (Ff.obj X), qX.obj (Ff.obj Y)) ≫
        TZ.map (Prod.mkHom (εh.app (Ff.obj X)) (εh.app (Ff.obj Y))) =
      Lh.map (rX.inv.app (⟨Ff.obj X, hFf X hx⟩, ⟨Ff.obj Y, hFf Y hy⟩)) ≫
        εh.app (tX.obj (Ff.obj X, Ff.obj Y)) ≫ qZ.map (bh.hom.app (Ff.obj X, Ff.obj Y)) ≫
        rZ.hom.app (⟨Fh.obj (Ff.obj X), hFh _ (hFf X hx)⟩,
          ⟨Fh.obj (Ff.obj Y), hFh _ (hFf Y hy)⟩) := by
      rw [← hσh _ _ (hFf X hx) (hFf Y hy), ← Lh.map_comp_assoc]
      simp
    have e₄ := εh.naturality (bf.hom.app (X, Y))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj,
      ObjectProperty.ι_obj] at e₁ e₂ e₄
    have e₅ : TZ.map (Prod.mkHom (w X) (w Y)) =
        TZ.map (Prod.mkHom (Lh.map (εf.app X)) (Lh.map (εf.app Y))) ≫
          TZ.map (Prod.mkHom (εh.app (Ff.obj X)) (εh.app (Ff.obj Y))) := by
      simp only [← TZ.map_comp, prod_comp, w]
    rw [e₅]
    simp only [Category.assoc]
    rw [reassoc_of% e₁]
    rw [← reassoc_of% e₂, e₃]
    simp only [← Lh.map_comp_assoc]
    rw [reassoc_of% (hσf X Y hx hy)]
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.map_comp]
    erw [Lh.map_id, Category.id_comp]
    rw [reassoc_of% e₄]
  simpa only [Category.assoc] using hl.trans hr.symm

/-- Descended tensor comparisons satisfy the composition law with the descended
compositor, at every pair of derived objects.
For all `A B : DY` the following square commutes:
```
  Lhf(A ⊗ B) ──────── σhf ────────→ Lhf A ⊗ Lhf B
      │ μ                                 │ μ ⊗ μ
      ↓                                   ↓
  Lh Lf(A ⊗ B) ─ Lh σf → Lh(Lf A ⊗ Lf B) ─ σh → Lh Lf A ⊗ Lh Lf B
```
Source: Stacks 07A4 and 0D6D (auxiliary; not a blueprint node).
Proof: both sides are components of natural transformations between the same functors
on pairs of derived objects. Restriction along the localization of pairs of
representatives is faithful, and on representatives the two components agree by
`tensorComparisonDescent_comp_app`. -/
theorem tensorComparisonDescent_comp
    (qY : KY ⥤ DY) (qX : KX ⥤ DX) (qZ : KZ ⥤ DZ)
    (Ff : KY ⥤ KX) (Fh : KX ⥤ KZ) (Fhf : KY ⥤ KZ)
    (Lf : DY ⥤ DX) (Lh : DX ⥤ DZ) (Lhf : DY ⥤ DZ)
    (εf : qY ⋙ Lf ⟶ Ff ⋙ qX) (εh : qX ⋙ Lh ⟶ Fh ⋙ qZ) (εhf : qY ⋙ Lhf ⟶ Fhf ⋙ qZ)
    (PY : ObjectProperty KY) (PX : ObjectProperty KX) (PZ : ObjectProperty KZ)
    (hFf : ∀ X, PY X → PX (Ff.obj X)) (hFh : ∀ X, PX X → PZ (Fh.obj X))
    (hFhf : ∀ X, PY X → PZ (Fhf.obj X))
    (hfaith : ((Functor.whiskeringLeft (PY.FullSubcategory × PY.FullSubcategory) (DY × DY)
      DZ).obj ((PY.ι ⋙ qY).prod (PY.ι ⋙ qY))).Faithful)
    (tY : KY × KY ⥤ KY) (tX : KX × KX ⥤ KX) (tZ : KZ × KZ ⥤ KZ)
    (TY : DY × DY ⥤ DY) (TX : DX × DX ⥤ DX) (TZ : DZ × DZ ⥤ DZ)
    (rY : (PY.ι.prod PY.ι) ⋙ tY ⋙ qY ≅ ((PY.ι ⋙ qY).prod (PY.ι ⋙ qY)) ⋙ TY)
    (rX : (PX.ι.prod PX.ι) ⋙ tX ⋙ qX ≅ ((PX.ι ⋙ qX).prod (PX.ι ⋙ qX)) ⋙ TX)
    (rZ : (PZ.ι.prod PZ.ι) ⋙ tZ ⋙ qZ ≅ ((PZ.ι ⋙ qZ).prod (PZ.ι ⋙ qZ)) ⋙ TZ)
    (bf : tY ⋙ Ff ≅ (Ff.prod Ff) ⋙ tX) (bh : tX ⋙ Fh ≅ (Fh.prod Fh) ⋙ tZ)
    (bhf : tY ⋙ Fhf ≅ (Fhf.prod Fhf) ⋙ tZ)
    (σf : TY ⋙ Lf ≅ (Lf.prod Lf) ⋙ TX) (σh : TX ⋙ Lh ≅ (Lh.prod Lh) ⋙ TZ)
    (σhf : TY ⋙ Lhf ≅ (Lhf.prod Lhf) ⋙ TZ)
    (hσf : ∀ (X Y : KY) (hx : PY X) (hy : PY Y),
      Lf.map (rY.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ σf.hom.app (qY.obj X, qY.obj Y) ≫
          TX.map (Prod.mkHom (εf.app X) (εf.app Y)) =
        εf.app (tY.obj (X, Y)) ≫ qX.map (bf.hom.app (X, Y)) ≫
          rX.hom.app (⟨Ff.obj X, hFf X hx⟩, ⟨Ff.obj Y, hFf Y hy⟩))
    (hσh : ∀ (X Y : KX) (hx : PX X) (hy : PX Y),
      Lh.map (rX.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ σh.hom.app (qX.obj X, qX.obj Y) ≫
          TZ.map (Prod.mkHom (εh.app X) (εh.app Y)) =
        εh.app (tX.obj (X, Y)) ≫ qZ.map (bh.hom.app (X, Y)) ≫
          rZ.hom.app (⟨Fh.obj X, hFh X hx⟩, ⟨Fh.obj Y, hFh Y hy⟩))
    (hσhf : ∀ (X Y : KY) (hx : PY X) (hy : PY Y),
      Lhf.map (rY.hom.app (⟨X, hx⟩, ⟨Y, hy⟩)) ≫ σhf.hom.app (qY.obj X, qY.obj Y) ≫
          TZ.map (Prod.mkHom (εhf.app X) (εhf.app Y)) =
        εhf.app (tY.obj (X, Y)) ≫ qZ.map (bhf.hom.app (X, Y)) ≫
          rZ.hom.app (⟨Fhf.obj X, hFhf X hx⟩, ⟨Fhf.obj Y, hFhf Y hy⟩))
    (m : Fhf ≅ Ff ⋙ Fh) (μ : Lhf ≅ Lf ⋙ Lh)
    (hμ : ∀ X : KY, εhf.app X ≫ qZ.map (m.hom.app X) =
      μ.hom.app (qY.obj X) ≫ Lh.map (εf.app X) ≫ εh.app (Ff.obj X))
    (hm : ∀ X Y : KY, bhf.hom.app (X, Y) ≫ tZ.map (Prod.mkHom (m.hom.app X) (m.hom.app Y)) =
      m.hom.app (tY.obj (X, Y)) ≫ Fh.map (bf.hom.app (X, Y)) ≫
        bh.hom.app (Ff.obj X, Ff.obj Y))
    (hεf : ∀ X, PY X → IsIso (εf.app X)) (hεh : ∀ X, PX X → IsIso (εh.app X))
    (A B : DY) :
    σhf.hom.app (A, B) ≫ TZ.map (Prod.mkHom (μ.hom.app A) (μ.hom.app B)) =
      μ.hom.app (TY.obj (A, B)) ≫ Lh.map (σf.hom.app (A, B)) ≫
        σh.hom.app (Lf.obj A, Lf.obj B) := by
  let N₁ : TY ⋙ Lhf ⟶ ((Lf ⋙ Lh).prod (Lf ⋙ Lh)) ⋙ TZ :=
    σhf.hom ≫ Functor.whiskerRight (NatTrans.prod μ.hom μ.hom) TZ
  let N₂ : TY ⋙ Lhf ⟶ ((Lf ⋙ Lh).prod (Lf ⋙ Lh)) ⋙ TZ :=
    Functor.whiskerLeft TY μ.hom ≫ Functor.whiskerRight σf.hom Lh ≫
      Functor.whiskerLeft (Lf.prod Lf) σh.hom
  have hN : N₁ = N₂ := by
    apply hfaith.map_injective
    ext ⟨⟨X, hx⟩, ⟨Y, hy⟩⟩
    exact tensorComparisonDescent_comp_app qY qX qZ Ff Fh Fhf Lf Lh Lhf εf εh εhf PY PX PZ
      hFf hFh hFhf tY tX tZ TY TX TZ rY rX rZ bf bh bhf σf σh σhf hσf hσh hσhf m μ hμ hm
      hεf hεh X Y hx hy
  exact congrArg (fun N ↦ N.app (A, B)) hN

/-- Transport of a descent square along identifications `F' ≅ F` of representative
functors and `L' ≅ L` of derived functors compatible with the factorizations.
Writing `σ_b` for `σ` conjugated by `b` and `c_p` for `c` conjugated by `p`, the
conclusion is the commutative square
```
  L qY(P ⊗ Q) ─ L mY → L(qY P ⊗ qY Q) ── σ_b ──→ L qY P ⊗ L qY Q
      │ ε                                              │ ε ⊗ ε
      ↓                                                ↓
  qX F(P ⊗ Q) ─ qX c_p → qX(F P ⊗ F Q) ─── mX ──→ qX F P ⊗ qX F Q
```
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: rewrite the transported comparison through the two bridges, move the bridges
across the source model by naturality and across the target model by its naturality,
and apply the original descent square. -/
theorem descentSquare_transport {KY KX DY DX : Type*} [Category KY] [Category KX]
    [Category DY] [Category DX] (qY : KY ⥤ DY) (qX : KX ⥤ DX) {F F' : KY ⥤ KX}
    {L L' : DY ⥤ DX} (ε : qY ⋙ L ⟶ F ⋙ qX) (ε' : qY ⋙ L' ⟶ F' ⋙ qX) (p : F' ≅ F)
    (b : L' ≅ L)
    (hb : ∀ A, ε'.app A ≫ qX.map (p.hom.app A) = b.hom.app (qY.obj A) ≫ ε.app A)
    (tY : KY × KY ⥤ KY) (tX : KX × KX ⥤ KX) (TY : DY × DY ⥤ DY) (TX : DX × DX ⥤ DX)
    (σ : TY ⋙ L' ≅ (L'.prod L') ⋙ TX) (c : tY ⋙ F' ≅ (F'.prod F') ⋙ tX) (P Q : KY)
    (mY : qY.obj (tY.obj (P, Q)) ⟶ TY.obj (qY.obj P, qY.obj Q))
    (mX' : qX.obj (tX.obj (F'.obj P, F'.obj Q)) ⟶ TX.obj (qX.obj (F'.obj P), qX.obj (F'.obj Q)))
    (mX : qX.obj (tX.obj (F.obj P, F.obj Q)) ⟶ TX.obj (qX.obj (F.obj P), qX.obj (F.obj Q)))
    (hr : qX.map (tX.map (Prod.mkHom (p.hom.app P) (p.hom.app Q))) ≫ mX =
      mX' ≫ TX.map (Prod.mkHom (qX.map (p.hom.app P)) (qX.map (p.hom.app Q))))
    (h₀ : L'.map mY ≫ σ.hom.app (qY.obj P, qY.obj Q) ≫
        TX.map (Prod.mkHom (ε'.app P) (ε'.app Q)) =
      ε'.app (tY.obj (P, Q)) ≫ qX.map (c.hom.app (P, Q)) ≫ mX') :
    L.map mY ≫ (b.inv.app (TY.obj (qY.obj P, qY.obj Q)) ≫ σ.hom.app (qY.obj P, qY.obj Q) ≫
        TX.map (Prod.mkHom (b.hom.app (qY.obj P)) (b.hom.app (qY.obj Q)))) ≫
        TX.map (Prod.mkHom (ε.app P) (ε.app Q)) =
      ε.app (tY.obj (P, Q)) ≫ qX.map (p.inv.app (tY.obj (P, Q)) ≫ c.hom.app (P, Q) ≫
        tX.map (Prod.mkHom (p.hom.app P) (p.hom.app Q))) ≫ mX := by
  have hT : TX.map (Prod.mkHom (b.hom.app (qY.obj P)) (b.hom.app (qY.obj Q))) ≫
      TX.map (Prod.mkHom (ε.app P) (ε.app Q)) =
      TX.map (Prod.mkHom (ε'.app P) (ε'.app Q)) ≫
        TX.map (Prod.mkHom (qX.map (p.hom.app P)) (qX.map (p.hom.app Q))) := by
    simp only [← TX.map_comp, prod_comp, hb]
  have hs : ε.app (tY.obj (P, Q)) ≫ qX.map (p.inv.app (tY.obj (P, Q))) =
      b.inv.app (qY.obj (tY.obj (P, Q))) ≫ ε'.app (tY.obj (P, Q)) := by
    rw [← cancel_epi (b.hom.app _), ← reassoc_of% (hb (tY.obj (P, Q)))]
    simp [← qX.map_comp]
  have hn := b.inv.naturality mY
  simp only [Category.assoc, hT, Functor.map_comp]
  rw [reassoc_of% hn, reassoc_of% h₀, ← hr, reassoc_of% hs]

end CategoryTheory
