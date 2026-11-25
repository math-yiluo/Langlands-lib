/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Basic

/-!
# Pasting laws in an exchange formalism

For a `CategoryTheory.ExchangeFormalism`, this file proves that the square
isomorphisms, the base change maps of the extension by zero and the exchange maps are
compatible with horizontal and vertical pasting of commutative squares.

The squares are written
```
U' --t--> U
|l        |r
Z' --b--> Z
```
with `t ≫ r = l ≫ b`; in the base change and exchange maps, `l` and `r` are open immersions.
Horizontal pasting composes the maps `t` and `b`, vertical pasting composes `l` and `r`.
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism

open TwoSquare

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section SqIso

/-- **Horizontal pasting of square isomorphisms.**
```
U'' --t₁--> U' --t₂--> U
|l          |m          |r
Z'' --b₁--> Z' --b₂--> Z
```
-/
@[reassoc]
lemma sqIso_hom_app_paste_horiz {U'' U' U Z'' Z' Z : 𝒞} (t₁ : U'' ⟶ U')
    (t₂ : U' ⟶ U) (l : U'' ⟶ Z'') (m : U' ⟶ Z') (r : U ⟶ Z) (b₁ : Z'' ⟶ Z') (b₂ : Z' ⟶ Z)
    (t : U'' ⟶ U) (b : Z'' ⟶ Z) (w₁ : t₁ ≫ m = l ≫ b₁) (w₂ : t₂ ≫ r = m ≫ b₂)
    (ht : t₁ ≫ t₂ = t) (hb : b₁ ≫ b₂ = b) (w : t ≫ r = l ≫ b) (M : F.obj Z) :
    (F.sqIso t l r b w).hom.app M =
      (F.pbComp' t₁ t₂ t ht).hom.app ((F.pb r).obj M) ≫
        (F.pb t₁).map ((F.sqIso t₂ m r b₂ w₂).hom.app M) ≫
        (F.sqIso t₁ l m b₁ w₁).hom.app ((F.pb b₂).obj M) ≫
        (F.pb l).map ((F.pbComp' b₁ b₂ b hb).inv.app M) := by
  have h₁ := F.pbComp'_assoc t₁ t₂ r t (t₂ ≫ r) (t ≫ r) ht rfl rfl M
  have hd : (t₁ ≫ m) ≫ b₂ = t ≫ r := by rw [Category.assoc, ← w₂, ← Category.assoc, ht]
  have h₂ := F.pbComp'_assoc t₁ m b₂ (t₁ ≫ m) (t₂ ≫ r) (t ≫ r) rfl w₂.symm hd M
  have h₃ := F.pbComp'_assoc l b₁ b₂ (t₁ ≫ m) b (t ≫ r) w₁.symm hb hd M
  rw [← cancel_epi ((F.pbComp' t r (t ≫ r) rfl).hom.app M)]
  simp only [sqIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_obj,
    Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← reassoc_of% h₂, Iso.hom_inv_id_app_assoc, reassoc_of% h₃,
    ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Vertical pasting of square isomorphisms.**
```
U' --t--> U
|l₁       |r₁
W' --h--> W
|l₂       |r₂
Z' --b--> Z
```
-/
@[reassoc]
lemma sqIso_hom_app_paste_vert {U' U W' W Z' Z : 𝒞} (t : U' ⟶ U) (h : W' ⟶ W)
    (b : Z' ⟶ Z) (l₁ : U' ⟶ W') (r₁ : U ⟶ W) (l₂ : W' ⟶ Z') (r₂ : W ⟶ Z) (l : U' ⟶ Z')
    (r : U ⟶ Z) (w₁ : t ≫ r₁ = l₁ ≫ h) (w₂ : h ≫ r₂ = l₂ ≫ b) (hl : l₁ ≫ l₂ = l)
    (hr : r₁ ≫ r₂ = r) (w : t ≫ r = l ≫ b) (M : F.obj Z) :
    (F.sqIso t l r b w).hom.app M =
      (F.pb t).map ((F.pbComp' r₁ r₂ r hr).hom.app M) ≫
        (F.sqIso t l₁ r₁ h w₁).hom.app ((F.pb r₂).obj M) ≫
        (F.pb l₁).map ((F.sqIso h l₂ r₂ b w₂).hom.app M) ≫
        (F.pbComp' l₁ l₂ l hl).inv.app ((F.pb b).obj M) := by
  have h₁ := F.pbComp'_assoc t r₁ r₂ (t ≫ r₁) r (t ≫ r) rfl hr (by rw [← hr, Category.assoc]) M
  have h₂ := F.pbComp'_assoc l₁ h r₂ (t ≫ r₁) (h ≫ r₂) (t ≫ r) w₁.symm rfl
    (by rw [← hr, ← Category.assoc]) M
  have h₃ := F.pbComp'_assoc l₁ l₂ b l (h ≫ r₂) (t ≫ r) hl w₂.symm
    (by rw [← hl, Category.assoc, ← w₂, ← Category.assoc, ← w₁, Category.assoc, hr]) M
  rw [← cancel_epi ((F.pbComp' t r (t ≫ r) rfl).hom.app M)]
  simp only [sqIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_obj,
    Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h₁, Iso.hom_inv_id_app_assoc, reassoc_of% h₂, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← reassoc_of% h₃,
    Iso.hom_inv_id_app, Category.comp_id]

end SqIso


section BaseChange

/-- **Horizontal pasting of base change maps.**
```
U'' --t₁--> U' --t₂--> U
|l          |m          |r
Z'' --b₁--> Z' --b₂--> Z
```
-/
lemma baseChange_paste_horiz {U'' U' U Z'' Z' Z : 𝒞} (t₁ : U'' ⟶ U')
    (t₂ : U' ⟶ U) (l : U'' ⟶ Z'') (m : U' ⟶ Z') (r : U ⟶ Z) (b₁ : Z'' ⟶ Z') (b₂ : Z' ⟶ Z)
    (t : U'' ⟶ U) (b : Z'' ⟶ Z) [Fact (𝒪 l)] [Fact (𝒪 m)] [Fact (𝒪 r)]
    (w₁ : t₁ ≫ m = l ≫ b₁) (w₂ : t₂ ≫ r = m ≫ b₂)
    (ht : t₁ ≫ t₂ = t) (hb : b₁ ≫ b₂ = b) (w : t ≫ r = l ≫ b) :
    F.baseChange t l r b w =
      ((F.baseChange t₂ m r b₂ w₂ ≫ₕ F.baseChange t₁ l m b₁ w₁).whiskerTop
        (F.pbComp' t₁ t₂ t ht).hom).whiskerBottom (F.pbComp' b₁ b₂ b hb).inv := by
  apply (mateEquiv (F.shAdj r) (F.shAdj l)).injective
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp _ (F.shAdj m)]
  simp only [baseChange, Equiv.apply_symm_apply]
  ext M
  simp [F.sqIso_hom_app_paste_horiz t₁ t₂ l m r b₁ b₂ t b w₁ w₂ ht hb w M]

/-- **Vertical pasting of base change maps.**
```
U' --t--> U
|l₁       |r₁
W' --h--> W
|l₂       |r₂
Z' --b--> Z
```
-/
lemma baseChange_paste_vert {U' U W' W Z' Z : 𝒞} (t : U' ⟶ U) (h : W' ⟶ W)
    (b : Z' ⟶ Z) (l₁ : U' ⟶ W') (r₁ : U ⟶ W) (l₂ : W' ⟶ Z') (r₂ : W ⟶ Z) (l : U' ⟶ Z')
    (r : U ⟶ Z) [Fact (𝒪 l₁)] [Fact (𝒪 r₁)] [Fact (𝒪 l₂)]
    [Fact (𝒪 r₂)] [Fact (𝒪 l)] [Fact (𝒪 r)]
    (w₁ : t ≫ r₁ = l₁ ≫ h) (w₂ : h ≫ r₂ = l₂ ≫ b) (hl : l₁ ≫ l₂ = l)
    (hr : r₁ ≫ r₂ = r) (w : t ≫ r = l ≫ b) :
    F.baseChange t l r b w =
      ((F.baseChange t l₁ r₁ h w₁ ≫ᵥ F.baseChange h l₂ r₂ b w₂).whiskerLeft
        (F.shComp' r₁ r₂ r hr).inv).whiskerRight (F.shComp' l₁ l₂ l hl).hom := by
  apply (mateEquiv (F.shAdj r) (F.shAdj l)).injective
  rw [mateEquiv_conjugateEquiv_vcomp _ ((F.shAdj l₁).comp (F.shAdj l₂)),
    conjugateEquiv_mateEquiv_vcomp _ ((F.shAdj r₁).comp (F.shAdj r₂)), mateEquiv_hcomp]
  have hr' : conjugateEquiv (F.shAdj r) ((F.shAdj r₁).comp (F.shAdj r₂))
      (F.shComp' r₁ r₂ r hr).inv = (F.pbComp' r₁ r₂ r hr).hom := by
    simp [shComp', conjugateIsoEquiv]
  have hl' : conjugateEquiv ((F.shAdj l₁).comp (F.shAdj l₂)) (F.shAdj l)
      (F.shComp' l₁ l₂ l hl).hom = (F.pbComp' l₁ l₂ l hl).inv := by
    simp [shComp', conjugateIsoEquiv]
  rw [hr', hl']
  simp only [baseChange, Equiv.apply_symm_apply]
  ext M
  simp [F.sqIso_hom_app_paste_vert t h b l₁ r₁ l₂ r₂ l r w₁ w₂ hl hr w M]

end BaseChange


section Exchange

/-- **Horizontal pasting of exchange maps.**
```
U'' --t₁--> U' --t₂--> U
|l          |m          |r
Z'' --b₁--> Z' --b₂--> Z
```
-/
lemma exchange_paste_horiz {U'' U' U Z'' Z' Z : 𝒞} (t₁ : U'' ⟶ U')
    (t₂ : U' ⟶ U) (l : U'' ⟶ Z'') (m : U' ⟶ Z') (r : U ⟶ Z) (b₁ : Z'' ⟶ Z') (b₂ : Z' ⟶ Z)
    (t : U'' ⟶ U) (b : Z'' ⟶ Z) [Fact (𝒪 l)] [Fact (𝒪 m)] [Fact (𝒪 r)]
    (w₁ : t₁ ≫ m = l ≫ b₁) (w₂ : t₂ ≫ r = m ≫ b₂)
    (ht : t₁ ≫ t₂ = t) (hb : b₁ ≫ b₂ = b) (w : t ≫ r = l ≫ b)
    [IsIso (F.baseChange t₁ l m b₁ w₁)] [IsIso (F.baseChange t₂ m r b₂ w₂)]
    [IsIso (F.baseChange t l r b w)] :
    F.exchange t l r b w =
      ((F.exchange t₁ l m b₁ w₁ ≫ₕ F.exchange t₂ m r b₂ w₂).whiskerTop
        (F.pfComp' t₁ t₂ t ht).hom).whiskerBottom (F.pfComp' b₁ b₂ b hb).inv := by
  have key : inv (F.baseChange t l r b w) =
      ((TwoSquare.vComp (TwoSquare.mk _ _ _ _ (inv (F.baseChange t₂ m r b₂ w₂)))
        (TwoSquare.mk _ _ _ _ (inv (F.baseChange t₁ l m b₁ w₁)))).whiskerLeft
          (F.pbComp' t₁ t₂ t ht).inv).whiskerRight (F.pbComp' b₁ b₂ b hb).hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_paste_horiz t₁ t₂ l m r b₁ b₂ t b w₁ w₂ ht hb w]
    ext M
    simp [← Functor.map_comp]
  have hP : conjugateEquiv (F.adj t) ((F.adj t₂).comp (F.adj t₁)) (F.pbComp' t₁ t₂ t ht).inv =
      (F.pfComp' t₁ t₂ t ht).hom := rfl
  have hP' : conjugateEquiv ((F.adj b₂).comp (F.adj b₁)) (F.adj b) (F.pbComp' b₁ b₂ b hb).hom =
      (F.pfComp' b₁ b₂ b hb).inv := rfl
  rw [exchange, key, mateEquiv_conjugateEquiv_vcomp _ ((F.adj b₂).comp (F.adj b₁)),
    conjugateEquiv_mateEquiv_vcomp _ ((F.adj t₂).comp (F.adj t₁)), mateEquiv_hcomp, hP, hP']
  rfl

/-- **Vertical pasting of exchange maps.**
```
U' --t--> U
|l₁       |r₁
W' --h--> W
|l₂       |r₂
Z' --b--> Z
```
-/
lemma exchange_paste_vert {U' U W' W Z' Z : 𝒞} (t : U' ⟶ U) (h : W' ⟶ W)
    (b : Z' ⟶ Z) (l₁ : U' ⟶ W') (r₁ : U ⟶ W) (l₂ : W' ⟶ Z') (r₂ : W ⟶ Z) (l : U' ⟶ Z')
    (r : U ⟶ Z) [Fact (𝒪 l₁)] [Fact (𝒪 r₁)] [Fact (𝒪 l₂)]
    [Fact (𝒪 r₂)] [Fact (𝒪 l)] [Fact (𝒪 r)]
    (w₁ : t ≫ r₁ = l₁ ≫ h) (w₂ : h ≫ r₂ = l₂ ≫ b) (hl : l₁ ≫ l₂ = l)
    (hr : r₁ ≫ r₂ = r) (w : t ≫ r = l ≫ b)
    [IsIso (F.baseChange t l₁ r₁ h w₁)] [IsIso (F.baseChange h l₂ r₂ b w₂)]
    [IsIso (F.baseChange t l r b w)] :
    F.exchange t l r b w =
      ((F.exchange t l₁ r₁ h w₁ ≫ᵥ F.exchange h l₂ r₂ b w₂).whiskerRight
        (F.shComp' r₁ r₂ r hr).hom).whiskerLeft (F.shComp' l₁ l₂ l hl).inv := by
  have key : inv (F.baseChange t l r b w) =
      ((TwoSquare.hComp (TwoSquare.mk _ _ _ _ (inv (F.baseChange t l₁ r₁ h w₁)))
        (TwoSquare.mk _ _ _ _ (inv (F.baseChange h l₂ r₂ b w₂)))).whiskerTop
          (F.shComp' r₁ r₂ r hr).hom).whiskerBottom (F.shComp' l₁ l₂ l hl).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_paste_vert t h b l₁ r₁ l₂ r₂ l r w₁ w₂ hl hr w]
    ext M
    simp [← Functor.map_comp_assoc]
  rw [exchange, key, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp _ (F.adj h)]
  rfl

end Exchange

end CategoryTheory.ExchangeFormalism
