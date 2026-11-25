/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data from gluing morphisms

Let `F` be a pseudofunctor from `LocallyDiscrete Cᵒᵖ` to `Cat`, `f i : X i ⟶ S` a family of
morphisms with chosen pullbacks `sq` and chosen threefold pullbacks `sq₃`. Given morphisms
`μ i : X i ⟶ W i`, objects `O i` over `W i` and *gluing morphisms*
`H i j : ((sq i j).p₁ ≫ μ i)^* (O i) ⟶ ((sq i j).p₂ ≫ μ j)^* (O j)` satisfying the identity and
cocycle conditions, we obtain a descent datum `DescentData'.ofGlue` for the objects
`(μ i)^* (O i)`.

We then compare an object `M` over `S` effectively descending such a descent datum with an object
`N` over another base `S'` mapping to `S`, along a family `f' i : X' i ⟶ S'` over the `f i`:
if the pullbacks of the gluing morphisms are induced by isomorphisms
`ε i : (m i)^* (O i) ≅ (f' i)^* N`, then `h^* M ≅ N`
(`DescentData'.nonempty_map_iso_of_ofGlue`), provided that `F.toDescentData f'` is fully
faithful.

This is used to glue modules of finite presentation descended to a finite stage of a cofiltered
limit of schemes.
-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Limits

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

lemma op_toLoc_comp_eq {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {fg : X ⟶ Z} (h : f ≫ g = fg) :
    g.op.toLoc ≫ f.op.toLoc = fg.op.toLoc := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` of a morphism conjugated by the comparison isomorphisms `mapComp'`. -/
lemma pullHom_mapComp'_conj ⦃X₁ X₂ X₁' X₂' : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ (r₁ : X₁' ⟶ X₁) (r₂ : X₂' ⟶ X₂) ⦃Y : C⦄ (p₁ : Y ⟶ X₁')
    (p₂ : Y ⟶ X₂') (x₁ : Y ⟶ X₁) (x₂ : Y ⟶ X₂) (hx₁ : p₁ ≫ r₁ = x₁) (hx₂ : p₂ ≫ r₂ = x₂)
    (ψ : (F.map x₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map x₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (l : Y' ⟶ Y) (f₁ : Y' ⟶ X₁') (f₂ : Y' ⟶ X₂') (hl₁ : l ≫ p₁ = f₁)
    (hl₂ : l ≫ p₂ = f₂) (y₁ : Y' ⟶ X₁) (y₂ : Y' ⟶ X₂) (hy₁ : f₁ ≫ r₁ = y₁)
    (hy₂ : f₂ ≫ r₂ = y₂) :
    pullHom ((F.mapComp' r₁.op.toLoc p₁.op.toLoc x₁.op.toLoc
        (op_toLoc_comp_eq hx₁)).inv.toNatTrans.app M₁ ≫ ψ ≫
        (F.mapComp' r₂.op.toLoc p₂.op.toLoc x₂.op.toLoc
          (op_toLoc_comp_eq hx₂)).hom.toNatTrans.app M₂) l f₁ f₂ hl₁ hl₂ =
      (F.mapComp' r₁.op.toLoc f₁.op.toLoc y₁.op.toLoc
          (op_toLoc_comp_eq hy₁)).inv.toNatTrans.app M₁ ≫
        pullHom ψ l y₁ y₂ (by rw [← hy₁, ← hx₁, ← hl₁, Category.assoc])
          (by rw [← hy₂, ← hx₂, ← hl₂, Category.assoc]) ≫
        (F.mapComp' r₂.op.toLoc f₂.op.toLoc y₂.op.toLoc
          (op_toLoc_comp_eq hy₂)).hom.toNatTrans.app M₂ := by
  subst hx₁ hx₂ hl₁ hl₂ hy₁ hy₂
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ rfl rfl (by cat_disch),
    mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ rfl rfl (by cat_disch)]

set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` of a comparison isomorphism `mapComp'` is a comparison isomorphism. -/
lemma pullHom_mapComp'_inv {S S' Y : C} (h : S' ⟶ S) (x : Y ⟶ S') (xh : Y ⟶ S)
    (hxh : x ≫ h = xh) (M : F.obj (.mk (op S))) ⦃Y' : C⦄ (g : Y' ⟶ Y) (gx : Y' ⟶ S')
    (gxh : Y' ⟶ S) (hgx : g ≫ x = gx) (hgxh : g ≫ xh = gxh) :
    pullHom (M₁ := (F.map h.op.toLoc).toFunctor.obj M) (M₂ := M)
        ((F.mapComp' h.op.toLoc x.op.toLoc xh.op.toLoc
          (op_toLoc_comp_eq hxh)).inv.toNatTrans.app M) g gx gxh hgx hgxh =
      (F.mapComp' h.op.toLoc gx.op.toLoc gxh.op.toLoc
        (op_toLoc_comp_eq (by rw [← hgxh, ← hxh, ← hgx, Category.assoc]))).inv.toNatTrans.app
          M := by
  subst hxh hgx hgxh
  dsimp [pullHom]
  rw [F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _ rfl rfl (by cat_disch)]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` of a morphism conjugated by the inverses of the comparison isomorphisms
`mapComp'`. -/
lemma pullHom_mapComp'_conj_symm ⦃X₁ X₂ X₁' X₂' : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ (p₁ : X₁' ⟶ X₁) (p₂ : X₂' ⟶ X₂) ⦃Y : C⦄ (r₁ : Y ⟶ X₁')
    (r₂ : Y ⟶ X₂') (x₁ : Y ⟶ X₁) (x₂ : Y ⟶ X₂) (hx₁ : r₁ ≫ p₁ = x₁) (hx₂ : r₂ ≫ p₂ = x₂)
    (ψ : (F.map r₁.op.toLoc).toFunctor.obj ((F.map p₁.op.toLoc).toFunctor.obj M₁) ⟶
      (F.map r₂.op.toLoc).toFunctor.obj ((F.map p₂.op.toLoc).toFunctor.obj M₂))
    ⦃Y' : C⦄ (l : Y' ⟶ Y) (z₁ : Y' ⟶ X₁') (z₂ : Y' ⟶ X₂') (hz₁ : l ≫ r₁ = z₁)
    (hz₂ : l ≫ r₂ = z₂) (y₁ : Y' ⟶ X₁) (y₂ : Y' ⟶ X₂) (hy₁ : z₁ ≫ p₁ = y₁)
    (hy₂ : z₂ ≫ p₂ = y₂) :
    pullHom ((F.mapComp' p₁.op.toLoc r₁.op.toLoc x₁.op.toLoc
        (op_toLoc_comp_eq hx₁)).hom.toNatTrans.app M₁ ≫ ψ ≫
        (F.mapComp' p₂.op.toLoc r₂.op.toLoc x₂.op.toLoc
          (op_toLoc_comp_eq hx₂)).inv.toNatTrans.app M₂) l y₁ y₂
        (by rw [← hy₁, ← hx₁, ← hz₁, Category.assoc])
        (by rw [← hy₂, ← hx₂, ← hz₂, Category.assoc]) =
      (F.mapComp' p₁.op.toLoc z₁.op.toLoc y₁.op.toLoc
          (op_toLoc_comp_eq hy₁)).hom.toNatTrans.app M₁ ≫
        pullHom ψ l z₁ z₂ hz₁ hz₂ ≫
        (F.mapComp' p₂.op.toLoc z₂.op.toLoc y₂.op.toLoc
          (op_toLoc_comp_eq hy₂)).inv.toNatTrans.app M₂ := by
  subst hx₁ hx₂ hz₁ hz₂ hy₁ hy₂
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc _ _ _ _ _ _ rfl rfl
      (by cat_disch),
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _ rfl rfl (by cat_disch)]

/-- Morphisms with equal pullbacks have equal `pullHom`s. -/
lemma pullHom_eq_pullHom_of_map_eq ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    {φ φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂)
    (h : (F.map g.op.toLoc).toFunctor.map φ = (F.map g.op.toLoc).toFunctor.map φ') :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ' g gf₁ gf₂ hgf₁ hgf₂ := by
  simp only [pullHom, h]

/-- Morphisms with equal `pullHom`s have equal pullbacks. -/
lemma map_eq_map_of_pullHom_eq ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    {φ φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) (h : pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ' g gf₁ gf₂ hgf₁ hgf₂) :
    (F.map g.op.toLoc).toFunctor.map φ = (F.map g.op.toLoc).toFunctor.map φ' := by
  rw [map_eq_pullHom φ g gf₁ gf₂ hgf₁ hgf₂, map_eq_pullHom φ' g gf₁ gf₂ hgf₁ hgf₂, h]


end LocallyDiscreteOpToCat

open LocallyDiscreteOpToCat

namespace DescentData'

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  (sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
  {W : ι → C} (μ : ∀ i, X i ⟶ W i) (O : ∀ i, F.obj (.mk (op (W i))))
  (H : ∀ i j, (F.map ((sq i j).p₁ ≫ μ i).op.toLoc).toFunctor.obj (O i) ⟶
    (F.map ((sq i j).p₂ ≫ μ j).op.toLoc).toFunctor.obj (O j))

/-- The morphisms of a descent datum for the objects `(μ i)^* (O i)` obtained from gluing
morphisms `H i j : ((sq i j).p₁ ≫ μ i)^* (O i) ⟶ ((sq i j).p₂ ≫ μ j)^* (O j)`, by conjugation
with the comparison isomorphisms `mapComp'`. -/
noncomputable def glueHom (i j : ι) :
    (F.map (sq i j).p₁.op.toLoc).toFunctor.obj ((F.map (μ i).op.toLoc).toFunctor.obj (O i)) ⟶
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj ((F.map (μ j).op.toLoc).toFunctor.obj (O j)) :=
  (F.mapComp' (μ i).op.toLoc (sq i j).p₁.op.toLoc ((sq i j).p₁ ≫ μ i).op.toLoc
      (op_toLoc_comp_eq rfl)).inv.toNatTrans.app (O i) ≫ H i j ≫
    (F.mapComp' (μ j).op.toLoc (sq i j).p₂.op.toLoc ((sq i j).p₂ ≫ μ j).op.toLoc
      (op_toLoc_comp_eq rfl)).hom.toNatTrans.app (O j)

lemma pullHom'_glueHom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (p : Y ⟶ (sq i₁ i₂).pullback)
    (hp₁ : p ≫ (sq i₁ i₂).p₁ = f₁) (hp₂ : p ≫ (sq i₁ i₂).p₂ = f₂) (y₁ : Y ⟶ W i₁)
    (y₂ : Y ⟶ W i₂) (hy₁ : f₁ ≫ μ i₁ = y₁) (hy₂ : f₂ ≫ μ i₂ = y₂) :
    pullHom' (glueHom μ O H) q f₁ f₂ hf₁ hf₂ =
      (F.mapComp' (μ i₁).op.toLoc f₁.op.toLoc y₁.op.toLoc
          (op_toLoc_comp_eq hy₁)).inv.toNatTrans.app (O i₁) ≫
        pullHom (H i₁ i₂) p y₁ y₂ (by rw [← hy₁, ← hp₁, Category.assoc])
          (by rw [← hy₂, ← hp₂, Category.assoc]) ≫
        (F.mapComp' (μ i₂).op.toLoc f₂.op.toLoc y₂.op.toLoc
          (op_toLoc_comp_eq hy₂)).hom.toNatTrans.app (O i₂) := by
  rw [pullHom'_eq_pullHom _ _ _ _ p hf₁ hf₂ hp₁ hp₂]
  exact pullHom_mapComp'_conj _ _ _ _ _ _ rfl rfl (H i₁ i₂) p f₁ f₂ hp₁ hp₂ y₁ y₂ hy₁ hy₂

variable {μ O} in
/-- The left hand side of the identity condition for gluing morphisms, along sections `d i` of
the diagonals. -/
noncomputable def glueSelfLHS (d : ∀ i, X i ⟶ (sq i i).pullback)
    (hd₁ : ∀ i, d i ≫ (sq i i).p₁ = 𝟙 _) (hd₂ : ∀ i, d i ≫ (sq i i).p₂ = 𝟙 _) (i : ι) :=
  pullHom (H i i) (d i) (μ i) (μ i) (by rw [reassoc_of% (hd₁ i)])
    (by rw [reassoc_of% (hd₂ i)])

variable {μ O H} in
/-- The identity condition for gluing morphisms, along sections `d i` of the diagonals. -/
def GlueSelf (d : ∀ i, X i ⟶ (sq i i).pullback) (hd₁ : ∀ i, d i ≫ (sq i i).p₁ = 𝟙 _)
    (hd₂ : ∀ i, d i ≫ (sq i i).p₂ = 𝟙 _) : Prop :=
  ∀ i, glueSelfLHS H d hd₁ hd₂ i = 𝟙 _

variable {μ O} in
/-- The left hand side of the cocycle condition for gluing morphisms. -/
noncomputable def glueCocLHS (i₁ i₂ i₃ : ι) :=
  pullHom (H i₁ i₂) (sq₃ i₁ i₂ i₃).p₁₂ ((sq₃ i₁ i₂ i₃).p₁ ≫ μ i₁)
      ((sq₃ i₁ i₂ i₃).p₂ ≫ μ i₂) (ChosenPullback₃.p₁₂_p₁_assoc _ _)
      (ChosenPullback₃.p₁₂_p₂_assoc _ _) ≫
    pullHom (H i₂ i₃) (sq₃ i₁ i₂ i₃).p₂₃ ((sq₃ i₁ i₂ i₃).p₂ ≫ μ i₂)
      ((sq₃ i₁ i₂ i₃).p₃ ≫ μ i₃) (ChosenPullback₃.p₂₃_p₂_assoc _ _)
      (ChosenPullback₃.p₂₃_p₃_assoc _ _)

variable {μ O} in
/-- The right hand side of the cocycle condition for gluing morphisms. -/
noncomputable def glueCocRHS (i₁ i₂ i₃ : ι) :=
  pullHom (H i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ ((sq₃ i₁ i₂ i₃).p₁ ≫ μ i₁)
      ((sq₃ i₁ i₂ i₃).p₃ ≫ μ i₃) (ChosenPullback₃.p₁₃_p₁_assoc _ _)
      (ChosenPullback₃.p₁₃_p₃_assoc _ _)

variable {μ O} in
/-- The cocycle condition for gluing morphisms. -/
def GlueCocycle : Prop :=
  ∀ i₁ i₂ i₃, glueCocLHS sq₃ H i₁ i₂ i₃ = glueCocRHS sq₃ H i₁ i₂ i₃

variable {d : ∀ i, X i ⟶ (sq i i).pullback} {hd₁ : ∀ i, d i ≫ (sq i i).p₁ = 𝟙 _}
  {hd₂ : ∀ i, d i ≫ (sq i i).p₂ = 𝟙 _}

set_option backward.isDefEq.respectTransparency false in
/-- **The descent datum defined by gluing morphisms** satisfying the identity and cocycle
conditions: the objects are `(μ i)^* (O i)`, and the morphisms are the gluing morphisms
conjugated with the comparison isomorphisms `mapComp'`. -/
noncomputable def ofGlue (hself : GlueSelf (H := H) d hd₁ hd₂) (hcoc : GlueCocycle sq₃ H) :
    F.DescentData' sq sq₃ where
  obj i := (F.map (μ i).op.toLoc).toFunctor.obj (O i)
  hom := glueHom μ O H
  pullHom'_hom_self i := by
    have hs := hself i
    rw [glueSelfLHS] at hs
    rw [pullHom'_glueHom μ O H (f i) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _)
      (d i) (hd₁ i) (hd₂ i) (μ i) (μ i) (Category.id_comp _) (Category.id_comp _), hs,
      Category.id_comp, Cat.Hom.inv_hom_id_toNatTrans_app]
    rfl
  pullHom'_hom_comp i₁ i₂ i₃ := by
    have hc := hcoc i₁ i₂ i₃
    rw [glueCocLHS, glueCocRHS] at hc
    rw [pullHom'_glueHom μ O H _ _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₂ (ChosenPullback₃.p₁₂_p₁ _)
        (ChosenPullback₃.p₁₂_p₂ _) _ _ rfl rfl,
      pullHom'_glueHom μ O H _ _ _ _ _ (sq₃ i₁ i₂ i₃).p₂₃ (ChosenPullback₃.p₂₃_p₂ _)
        (ChosenPullback₃.p₂₃_p₃ _) _ _ rfl rfl,
      pullHom'_glueHom μ O H _ _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₃ (ChosenPullback₃.p₁₃_p₁ _)
        (ChosenPullback₃.p₁₃_p₃ _) _ _ rfl rfl, ← hc]
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

@[simp]
lemma ofGlue_obj (hself : GlueSelf (H := H) d hd₁ hd₂) (hcoc : GlueCocycle sq₃ H) (i : ι) :
    (ofGlue sq₃ μ O H hself hcoc).obj i = (F.map (μ i).op.toLoc).toFunctor.obj (O i) := rfl

lemma ofGlue_hom (hself : GlueSelf (H := H) d hd₁ hd₂) (hcoc : GlueCocycle sq₃ H) :
    (ofGlue sq₃ μ O H hself hcoc).hom = glueHom μ O H := rfl

variable {sq₃ μ O H}

/-- The components of an isomorphism from the descent datum of `M` to the descent datum
`ofGlue`, pulled back to the chosen pullbacks, are compatible with the gluing morphisms. -/
lemma pullHom_comp_eq_of_iso_ofGlue {hself : GlueSelf (H := H) d hd₁ hd₂}
    {hcoc : GlueCocycle sq₃ H} {M : F.obj (.mk (op S))}
    (e : (F.toDescentData f).obj M ⟶ (ofGlue sq₃ μ O H hself hcoc).descentData) (i j : ι) :
    pullHom (e.hom i) (sq i j).p₁ (sq i j).p ((sq i j).p₁ ≫ μ i) (by simp) rfl ≫ H i j =
      pullHom (e.hom j) (sq i j).p₂ (sq i j).p ((sq i j).p₂ ≫ μ j) (by simp) rfl := by
  have hc := e.comm (sq i j).p (sq i j).p₁ (sq i j).p₂ (by simp) (by simp)
  rw [map_eq_pullHom (e.hom i) (sq i j).p₁ (sq i j).p ((sq i j).p₁ ≫ μ i) (by simp) rfl,
    map_eq_pullHom (e.hom j) (sq i j).p₂ (sq i j).p ((sq i j).p₂ ≫ μ j) (by simp) rfl] at hc
  rw [descentData_hom, ofGlue_hom, pullHom'_glueHom μ O H _ _ _ _ _ (𝟙 _) (Category.id_comp _)
    (Category.id_comp _) _ _ rfl rfl, pullHom_id] at hc
  erw [DescentData.ofObj_hom] at hc
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc] at hc
  rw [← cancel_epi ((F.mapComp' (f i).op.toLoc (sq i j).p₁.op.toLoc (sq i j).p.op.toLoc
    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app M),
    ← cancel_mono ((F.mapComp' (μ j).op.toLoc (sq i j).p₂.op.toLoc
      ((sq i j).p₂ ≫ μ j).op.toLoc (op_toLoc_comp_eq rfl)).hom.toNatTrans.app (O j))]
  simpa only [Category.assoc] using hc

end DescentData'

/-- **Gluing isomorphisms.** If `F.toDescentData f` is fully faithful, isomorphisms between the
pullbacks of two objects along the `f i` which agree on the chosen pullbacks come from an
isomorphism between the objects. -/
lemma nonempty_iso_of_pullHom_eq {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (hf : ∀ M N : F.obj (.mk (op S)),
      Function.Bijective ((F.toDescentData f).map : (M ⟶ N) → _))
    {M N : F.obj (.mk (op S))}
    (σ : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj M ≅ (F.map (f i).op.toLoc).toFunctor.obj N)
    (hσ : ∀ i j, pullHom (σ i).hom (sq i j).p₁ (sq i j).p (sq i j).p (by simp) (by simp) =
      pullHom (σ j).hom (sq i j).p₂ (sq i j).p (sq i j).p (by simp) (by simp)) :
    Nonempty (M ≅ N) := by
  have key ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
      pullHom (σ i₁).hom f₁ q q hf₁ hf₁ = pullHom (σ i₂).hom f₂ q q hf₂ hf₂ := by
    obtain ⟨l, hl₁, hl₂⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by rw [hf₁, hf₂])
    have hl : l ≫ (sq i₁ i₂).p = q := by rw [← (sq i₁ i₂).hp₁, reassoc_of% hl₁, hf₁]
    rw [pullHom_congr_left (σ i₁).hom hl₁.symm q q hf₁ hf₁,
      pullHom_congr_left (σ i₂).hom hl₂.symm q q hf₂ hf₂,
      ← pullHom_pullHom (σ i₁).hom (sq i₁ i₂).p₁ (sq i₁ i₂).p (sq i₁ i₂).p l q q,
      ← pullHom_pullHom (σ i₂).hom (sq i₁ i₂).p₂ (sq i₁ i₂).p (sq i₁ i₂).p l q q, hσ]
  let E : (F.toDescentData f).obj M ≅ (F.toDescentData f).obj N :=
    DescentData.isoMk σ (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
      erw [DescentData.ofObj_hom, DescentData.ofObj_hom]
      rw [map_eq_pullHom (σ i₁).hom f₁ q q hf₁ hf₁, map_eq_pullHom (σ i₂).hom f₂ q q hf₂ hf₂,
        key q f₁ f₂ hf₁ hf₂]
      simp)
  obtain ⟨a, ha⟩ := (hf M N).2 E.hom
  obtain ⟨b, hb⟩ := (hf N M).2 E.inv
  exact ⟨⟨a, b, (hf M M).1 (by rw [Functor.map_comp, ha, hb, E.hom_inv_id, Functor.map_id]),
    (hf N N).1 (by rw [Functor.map_comp, ha, hb, E.inv_hom_id, Functor.map_id])⟩⟩

namespace DescentData'

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  {sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}
  {W : ι → C} {μ : ∀ i, X i ⟶ W i} {O : ∀ i, F.obj (.mk (op (W i)))}
  {H : ∀ i j, (F.map ((sq i j).p₁ ≫ μ i).op.toLoc).toFunctor.obj (O i) ⟶
    (F.map ((sq i j).p₂ ≫ μ j).op.toLoc).toFunctor.obj (O j)}
  {d : ∀ i, X i ⟶ (sq i i).pullback} {hd₁ : ∀ i, d i ≫ (sq i i).p₁ = 𝟙 _}
  {hd₂ : ∀ i, d i ≫ (sq i i).p₂ = 𝟙 _}

set_option backward.isDefEq.respectTransparency false in
/-- **Comparison with a glued object.** Let `M` over `S` effectively descend the descent datum
defined by gluing morphisms `H`. Let `h : S' ⟶ S` and `f' i : X' i ⟶ S'` be a family over the
`f i` (via `r i : X' i ⟶ X i`, and `r₂ i j` on the chosen pullbacks), for which
`F.toDescentData f'` is fully faithful. If `N` over `S'` comes with isomorphisms
`ε i : (m i)^* (O i) ≅ (f' i)^* N`, where `m i = r i ≫ μ i`, inducing the pullbacks of the gluing
morphisms, then `h^* M ≅ N`. -/
theorem nonempty_map_iso_of_ofGlue {hself : GlueSelf (H := H) d hd₁ hd₂}
    {hcoc : GlueCocycle sq₃ H} {M : F.obj (.mk (op S))}
    (e : (F.toDescentData f).obj M ≅ (ofGlue sq₃ μ O H hself hcoc).descentData)
    {S' : C} {X' : ι → C} {f' : ∀ i, X' i ⟶ S'} (sq' : ∀ i j, ChosenPullback (f' i) (f' j))
    (hf' : ∀ M N : F.obj (.mk (op S')),
      Function.Bijective ((F.toDescentData f').map : (M ⟶ N) → _))
    (h : S' ⟶ S) (r : ∀ i, X' i ⟶ X i) (hr : ∀ i, r i ≫ f i = f' i ≫ h)
    (r₂ : ∀ i j, (sq' i j).pullback ⟶ (sq i j).pullback)
    (hr₂₁ : ∀ i j, r₂ i j ≫ (sq i j).p₁ = (sq' i j).p₁ ≫ r i)
    (hr₂₂ : ∀ i j, r₂ i j ≫ (sq i j).p₂ = (sq' i j).p₂ ≫ r j)
    (m : ∀ i, X' i ⟶ W i) (hm : ∀ i, r i ≫ μ i = m i) (N : F.obj (.mk (op S')))
    (ε : ∀ i, (F.map (m i).op.toLoc).toFunctor.obj (O i) ≅
      (F.map (f' i).op.toLoc).toFunctor.obj N)
    (hε : ∀ i j, pullHom (H i j) (r₂ i j) ((sq' i j).p₁ ≫ m i) ((sq' i j).p₂ ≫ m j)
        (by rw [reassoc_of% (hr₂₁ i j), hm]) (by rw [reassoc_of% (hr₂₂ i j), hm]) =
      pullHom (ε i).hom (sq' i j).p₁ ((sq' i j).p₁ ≫ m i) (sq' i j).p rfl (by simp) ≫
        pullHom (ε j).inv (sq' i j).p₂ (sq' i j).p ((sq' i j).p₂ ≫ m j) (by simp) rfl) :
    Nonempty ((F.map h.op.toLoc).toFunctor.obj M ≅ N) := by
  let l (i : ι) : (F.map (f i).op.toLoc).toFunctor.obj M ≅
      (F.map (μ i).op.toLoc).toFunctor.obj (O i) :=
    { hom := e.hom.hom i
      inv := e.inv.hom i
      hom_inv_id := by rw [← DescentData.comp_hom, e.hom_inv_id]; rfl
      inv_hom_id := by rw [← DescentData.comp_hom, e.inv_hom_id]; rfl }
  have hl : ∀ i j, pullHom (l i).hom (sq i j).p₁ (sq i j).p ((sq i j).p₁ ≫ μ i) (by simp) rfl ≫
      H i j = pullHom (l j).hom (sq i j).p₂ (sq i j).p ((sq i j).p₂ ≫ μ j) (by simp) rfl :=
    pullHom_comp_eq_of_iso_ofGlue e.hom
  let κ (i : ι) : (F.map (f' i).op.toLoc).toFunctor.obj ((F.map h.op.toLoc).toFunctor.obj M) ≅
      (F.map (f' i ≫ h).op.toLoc).toFunctor.obj M :=
    { hom := (F.mapComp' h.op.toLoc (f' i).op.toLoc (f' i ≫ h).op.toLoc
        (op_toLoc_comp_eq rfl)).inv.toNatTrans.app M
      inv := (F.mapComp' h.op.toLoc (f' i).op.toLoc (f' i ≫ h).op.toLoc
        (op_toLoc_comp_eq rfl)).hom.toNatTrans.app M
      hom_inv_id := by simp
      inv_hom_id := by simp }
  let ρ (i : ι) : (F.map (f' i ≫ h).op.toLoc).toFunctor.obj M ≅
      (F.map (m i).op.toLoc).toFunctor.obj (O i) :=
    { hom := pullHom (l i).hom (r i) (f' i ≫ h) (m i) (hr i) (hm i)
      inv := pullHom (l i).inv (r i) (m i) (f' i ≫ h) (hm i) (hr i)
      hom_inv_id := by rw [← pullHom_comp, Iso.hom_inv_id, pullHom_id_eq_id]
      inv_hom_id := by rw [← pullHom_comp, Iso.inv_hom_id, pullHom_id_eq_id] }
  let σ (i : ι) := κ i ≪≫ ρ i ≪≫ ε i
  have hq (i j : ι) : r₂ i j ≫ (sq i j).p = (sq' i j).p ≫ h := by
    rw [← (sq i j).hp₁, reassoc_of% (hr₂₁ i j), hr, ← Category.assoc, (sq' i j).hp₁]
  -- the pullback of `(l i).hom` to the chosen pullbacks
  have hρ₁ (i j : ι) : pullHom (pullHom (l i).hom (r i) (f' i ≫ h) (m i) (hr i) (hm i))
      (sq' i j).p₁ ((sq' i j).p ≫ h) ((sq' i j).p₁ ≫ m i) (by simp) rfl =
      pullHom (pullHom (l i).hom (sq i j).p₁ (sq i j).p ((sq i j).p₁ ≫ μ i) (by simp) rfl)
        (r₂ i j) ((sq' i j).p ≫ h) ((sq' i j).p₁ ≫ m i) (hq i j)
        (by rw [reassoc_of% (hr₂₁ i j), hm]) := by
    rw [pullHom_pullHom, pullHom_pullHom]
    exact pullHom_congr_left _ (hr₂₁ i j).symm _ _ _ _
  have hρ₂ (i j : ι) : pullHom (pullHom (l j).hom (r j) (f' j ≫ h) (m j) (hr j) (hm j))
      (sq' i j).p₂ ((sq' i j).p ≫ h) ((sq' i j).p₂ ≫ m j) (by simp) rfl =
      pullHom (pullHom (l j).hom (sq i j).p₂ (sq i j).p ((sq i j).p₂ ≫ μ j) (by simp) rfl)
        (r₂ i j) ((sq' i j).p ≫ h) ((sq' i j).p₂ ≫ m j) (hq i j)
        (by rw [reassoc_of% (hr₂₂ i j), hm]) := by
    rw [pullHom_pullHom, pullHom_pullHom]
    exact pullHom_congr_left _ (hr₂₂ i j).symm _ _ _ _
  refine nonempty_iso_of_pullHom_eq sq' hf' σ fun i j ↦ ?_
  simp only [σ, κ, ρ, Iso.trans_hom]
  rw [pullHom_comp _ _ (sq' i j).p₁ (sq' i j).p ((sq' i j).p ≫ h) (sq' i j).p (by simp)
      (by simp) (by simp),
    pullHom_comp _ _ (sq' i j).p₁ ((sq' i j).p ≫ h) ((sq' i j).p₁ ≫ m i) (sq' i j).p
      (by simp) rfl (by simp),
    pullHom_comp _ _ (sq' i j).p₂ (sq' i j).p ((sq' i j).p ≫ h) (sq' i j).p (by simp)
      (by simp) (by simp),
    pullHom_comp _ _ (sq' i j).p₂ ((sq' i j).p ≫ h) ((sq' i j).p₂ ≫ m j) (sq' i j).p
      (by simp) rfl (by simp),
    pullHom_mapComp'_inv (hxh := rfl), pullHom_mapComp'_inv (hxh := rfl), hρ₁, hρ₂]
  have hε' : pullHom (ε i).hom (sq' i j).p₁ ((sq' i j).p₁ ≫ m i) (sq' i j).p rfl (by simp) =
      pullHom (H i j) (r₂ i j) ((sq' i j).p₁ ≫ m i) ((sq' i j).p₂ ≫ m j)
        (by rw [reassoc_of% (hr₂₁ i j), hm]) (by rw [reassoc_of% (hr₂₂ i j), hm]) ≫
      pullHom (ε j).hom (sq' i j).p₂ ((sq' i j).p₂ ≫ m j) (sq' i j).p rfl (by simp) := by
    rw [hε, Category.assoc, ← pullHom_comp, Iso.inv_hom_id, pullHom_id_eq_id, Category.comp_id]
  rw [hε', ← pullHom_comp_assoc, hl i j]

section IsoGlueHom

variable (sq) {N : F.obj (.mk (op S))}
  (ε : ∀ i, (F.map (μ i).op.toLoc).toFunctor.obj (O i) ≅ (F.map (f i).op.toLoc).toFunctor.obj N)

/-- The gluing morphisms induced by isomorphisms `ε i : (μ i)^* (O i) ≅ (f i)^* N`. -/
noncomputable def isoGlueHom (i j : ι) :
    (F.map ((sq i j).p₁ ≫ μ i).op.toLoc).toFunctor.obj (O i) ⟶
      (F.map ((sq i j).p₂ ≫ μ j).op.toLoc).toFunctor.obj (O j) :=
  pullHom (ε i).hom (sq i j).p₁ ((sq i j).p₁ ≫ μ i) (sq i j).p rfl (by simp) ≫
    pullHom (ε j).inv (sq i j).p₂ (sq i j).p ((sq i j).p₂ ≫ μ j) (by simp) rfl

variable {sq}

lemma glueSelf_isoGlueHom (d : ∀ i, X i ⟶ (sq i i).pullback)
    (hd₁ : ∀ i, d i ≫ (sq i i).p₁ = 𝟙 _) (hd₂ : ∀ i, d i ≫ (sq i i).p₂ = 𝟙 _) :
    GlueSelf (H := isoGlueHom sq ε) d hd₁ hd₂ := fun i ↦ by
  have hp : d i ≫ (sq i i).p = f i := by rw [← (sq i i).hp₁, reassoc_of% (hd₁ i)]
  rw [glueSelfLHS, isoGlueHom,
    pullHom_comp _ _ _ _ (f i) _ (by rw [reassoc_of% (hd₁ i)]) (by simp [hp])
      (by rw [reassoc_of% (hd₂ i)]), pullHom_pullHom, pullHom_pullHom,
    pullHom_congr_left _ (hd₁ i) _ _ _ _, pullHom_congr_left (ε i).inv (hd₂ i) _ _ _ _,
    pullHom_id, pullHom_id, Iso.hom_inv_id]

lemma glueCocycle_isoGlueHom : GlueCocycle sq₃ (isoGlueHom sq ε) := fun i₁ i₂ i₃ ↦ by
  simp only [glueCocLHS, glueCocRHS, isoGlueHom]
  rw [pullHom_comp _ _ _ _ (sq₃ i₁ i₂ i₃).p _ (ChosenPullback₃.p₁₂_p₁_assoc _ _) (by simp)
      (ChosenPullback₃.p₁₂_p₂_assoc _ _),
    pullHom_comp _ _ _ _ (sq₃ i₁ i₂ i₃).p _ (ChosenPullback₃.p₂₃_p₂_assoc _ _) (by simp)
      (ChosenPullback₃.p₂₃_p₃_assoc _ _),
    pullHom_comp _ _ _ _ (sq₃ i₁ i₂ i₃).p _ (ChosenPullback₃.p₁₃_p₁_assoc _ _) (by simp)
      (ChosenPullback₃.p₁₃_p₃_assoc _ _)]
  simp only [pullHom_pullHom, Category.assoc]
  rw [pullHom_congr_left (ε i₂).inv (ChosenPullback₃.p₁₂_p₂ (sq₃ i₁ i₂ i₃)) _ _ _ _,
    pullHom_congr_left (ε i₂).hom (ChosenPullback₃.p₂₃_p₂ (sq₃ i₁ i₂ i₃)) _ _ _ _,
    ← pullHom_comp_assoc, Iso.inv_hom_id, pullHom_id_eq_id, Category.id_comp,
    pullHom_congr_left (ε i₁).hom (ChosenPullback₃.p₁₂_p₁ (sq₃ i₁ i₂ i₃)) _ _ _ _,
    pullHom_congr_left (ε i₁).hom (ChosenPullback₃.p₁₃_p₁ (sq₃ i₁ i₂ i₃)) _ _ _ _,
    pullHom_congr_left (ε i₃).inv (ChosenPullback₃.p₂₃_p₃ (sq₃ i₁ i₂ i₃)) _ _ _ _,
    pullHom_congr_left (ε i₃).inv (ChosenPullback₃.p₁₃_p₃ (sq₃ i₁ i₂ i₃)) _ _ _ _]

end IsoGlueHom

section Pull

variable {S' : C} {X' : ι → C} {f' : ∀ i, X' i ⟶ S'} {sq' : ∀ i j, ChosenPullback (f' i) (f' j)}
  {r : ∀ i, X' i ⟶ X i} (r₂ : ∀ i j, (sq' i j).pullback ⟶ (sq i j).pullback)
  (hr₂₁ : ∀ i j, r₂ i j ≫ (sq i j).p₁ = (sq' i j).p₁ ≫ r i)
  (hr₂₂ : ∀ i j, r₂ i j ≫ (sq i j).p₂ = (sq' i j).p₂ ≫ r j)
  {μ' : ∀ i, X' i ⟶ W i} (hμ : ∀ i, r i ≫ μ i = μ' i)

/-- The pullback of gluing morphisms along morphisms `r₂ i j` between the chosen pullbacks of
two families, compatible with morphisms `r i` between their members. -/
noncomputable def pullGlue (i j : ι) :
    (F.map ((sq' i j).p₁ ≫ μ' i).op.toLoc).toFunctor.obj (O i) ⟶
      (F.map ((sq' i j).p₂ ≫ μ' j).op.toLoc).toFunctor.obj (O j) :=
  pullHom (H i j) (r₂ i j) _ _ (by rw [reassoc_of% (hr₂₁ i j), hμ])
    (by rw [reassoc_of% (hr₂₂ i j), hμ])

lemma pullHom_glueSelfLHS (d' : ∀ i, X' i ⟶ (sq' i i).pullback)
    (hd'₁ : ∀ i, d' i ≫ (sq' i i).p₁ = 𝟙 _) (hd'₂ : ∀ i, d' i ≫ (sq' i i).p₂ = 𝟙 _)
    (hd : ∀ i, d' i ≫ r₂ i i = r i ≫ d i) (i : ι) :
    pullHom (glueSelfLHS H d hd₁ hd₂ i) (r i) (μ' i) (μ' i) (hμ i) (hμ i) =
      glueSelfLHS (pullGlue (H := H) r₂ hr₂₁ hr₂₂ hμ) d' hd'₁ hd'₂ i := by
  rw [glueSelfLHS, glueSelfLHS, pullGlue, pullHom_pullHom, pullHom_pullHom]
  exact pullHom_congr_left _ (hd i).symm _ _ _ _

variable (sq₃) {sq₃' : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq' i₁ i₂) (sq' i₂ i₃) (sq' i₁ i₃)}
  (r₃ : ∀ i₁ i₂ i₃, (sq₃' i₁ i₂ i₃).pullback ⟶ (sq₃ i₁ i₂ i₃).pullback)
  (h₁₂ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₁₂ = (sq₃' i₁ i₂ i₃).p₁₂ ≫ r₂ i₁ i₂)
  (h₂₃ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₂₃ = (sq₃' i₁ i₂ i₃).p₂₃ ≫ r₂ i₂ i₃)
  (h₁₃ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₁₃ = (sq₃' i₁ i₂ i₃).p₁₃ ≫ r₂ i₁ i₃)
  (hr₃₁ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₁ = (sq₃' i₁ i₂ i₃).p₁ ≫ r i₁)
  (hr₃₂ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₂ = (sq₃' i₁ i₂ i₃).p₂ ≫ r i₂)
  (hr₃₃ : ∀ i₁ i₂ i₃, r₃ i₁ i₂ i₃ ≫ (sq₃ i₁ i₂ i₃).p₃ = (sq₃' i₁ i₂ i₃).p₃ ≫ r i₃)

include h₁₂ h₂₃ hr₃₂ in
lemma pullHom_glueCocLHS (i₁ i₂ i₃ : ι) :
    pullHom (glueCocLHS sq₃ H i₁ i₂ i₃) (r₃ i₁ i₂ i₃) ((sq₃' i₁ i₂ i₃).p₁ ≫ μ' i₁)
        ((sq₃' i₁ i₂ i₃).p₃ ≫ μ' i₃) (by rw [reassoc_of% (hr₃₁ i₁ i₂ i₃), hμ])
        (by rw [reassoc_of% (hr₃₃ i₁ i₂ i₃), hμ]) =
      glueCocLHS sq₃' (pullGlue (H := H) r₂ hr₂₁ hr₂₂ hμ) i₁ i₂ i₃ := by
  rw [glueCocLHS, glueCocLHS, pullHom_comp _ _ _ _ ((sq₃' i₁ i₂ i₃).p₂ ≫ μ' i₂) _
    (by rw [reassoc_of% (hr₃₁ i₁ i₂ i₃), hμ]) (by rw [reassoc_of% (hr₃₂ i₁ i₂ i₃), hμ])
    (by rw [reassoc_of% (hr₃₃ i₁ i₂ i₃), hμ]), pullGlue, pullGlue,
    pullHom_pullHom, pullHom_pullHom, pullHom_pullHom, pullHom_pullHom]
  exact congrArg₂ (· ≫ ·) (pullHom_congr_left _ (h₁₂ i₁ i₂ i₃) _ _ _ _)
    (pullHom_congr_left _ (h₂₃ i₁ i₂ i₃) _ _ _ _)

include h₁₃ in
lemma pullHom_glueCocRHS (i₁ i₂ i₃ : ι) :
    pullHom (glueCocRHS sq₃ H i₁ i₂ i₃) (r₃ i₁ i₂ i₃) ((sq₃' i₁ i₂ i₃).p₁ ≫ μ' i₁)
        ((sq₃' i₁ i₂ i₃).p₃ ≫ μ' i₃) (by rw [reassoc_of% (hr₃₁ i₁ i₂ i₃), hμ])
        (by rw [reassoc_of% (hr₃₃ i₁ i₂ i₃), hμ]) =
      glueCocRHS sq₃' (pullGlue (H := H) r₂ hr₂₁ hr₂₂ hμ) i₁ i₂ i₃ := by
  rw [glueCocRHS, glueCocRHS, pullGlue, pullHom_pullHom, pullHom_pullHom]
  exact pullHom_congr_left _ (h₁₃ i₁ i₂ i₃) _ _ _ _

end Pull

end DescentData'

end CategoryTheory.Pseudofunctor
