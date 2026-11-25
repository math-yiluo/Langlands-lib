/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Identity
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Pasting

/-!
# Base change maps on a cube in a exchange formalism

Consider a commutative cube of schemes whose top face is the square
```
U' --t--> U
|l        |r
Z' --b--> Z
```
and whose bottom face is a square `t' ≫ r' = l' ≫ b'` mapping to it through
`x : V' ⟶ U'`, `y : V ⟶ U`, `z : W' ⟶ Z'` and `v : W ⟶ Z`, with `l`, `r`, `l'`, `r'` open
immersions. The base change map of the extension by zero of the diagonal square
`(x ≫ t) ≫ r = l' ≫ (z ≫ b)` decomposes in two ways as a horizontal pasting, through the top face
or through the bottom face. Comparing the two decompositions gives a relation between the base
change maps of the top face, of the bottom face and of the two side faces containing the open
immersions (`CategoryTheory.ExchangeFormalism.baseChange_cube`).
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism

open TwoSquare

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

/-- **The base change maps on a commutative cube.** For a commutative cube with top face
`t ≫ r = l ≫ b`, bottom face `t' ≫ r' = l' ≫ b'` and connecting maps `x`, `y`, `z`, `v`
```
V' --t'--> V           U' --t--> U
|l'        |r'   ⟶     |l        |r
W' --b'--> W           Z' --b--> Z
```
the base change maps of the top face, of the face `x ≫ l = l' ≫ z` and the square isomorphisms
of the faces `x ≫ t = t' ≫ y` and `z ≫ b = b' ≫ v` compose to the base change maps of the bottom
face and of the face `y ≫ r = r' ≫ v`. -/
lemma baseChange_cube {U' U Z' Z V' V W' W : 𝒞} (t : U' ⟶ U) (l : U' ⟶ Z')
    (r : U ⟶ Z) (b : Z' ⟶ Z) (t' : V' ⟶ V) (l' : V' ⟶ W') (r' : V ⟶ W) (b' : W' ⟶ W)
    (x : V' ⟶ U') (y : V ⟶ U) (z : W' ⟶ Z') (v : W ⟶ Z) [Fact (𝒪 l)]
    [Fact (𝒪 r)] [Fact (𝒪 l')] [Fact (𝒪 r')] (w : t ≫ r = l ≫ b)
    (w' : t' ≫ r' = l' ≫ b') (sx : x ≫ t = t' ≫ y) (sl : x ≫ l = l' ≫ z)
    (sr : y ≫ r = r' ≫ v) (sb : z ≫ b = b' ≫ v) (M : F.obj U) :
    (F.sh l').map ((F.sqIso x t' t y sx).inv.app M) ≫
        (F.baseChange x l' l z sl).app ((F.pb t).obj M) ≫
        (F.pb z).map ((F.baseChange t l r b w).app M) ≫
        (F.sqIso z b' b v sb).hom.app ((F.sh r).obj M) =
      (F.baseChange t' l' r' b' w').app ((F.pb y).obj M) ≫
        (F.pb b').map ((F.baseChange y r' r v sr).app M) := by
  have wbig : (x ≫ t) ≫ r = l' ≫ z ≫ b := by
    rw [Category.assoc, w, reassoc_of% sl]
  have h₁ := congr_app (F.baseChange_paste_horiz x t l' l r z b (x ≫ t) (z ≫ b) sl w rfl rfl
    wbig) M
  have h₂ := congr_app (F.baseChange_paste_horiz t' y l' r' r b' v (x ≫ t) (z ≫ b) w' sr
    sx.symm sb.symm wbig) M
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj, Category.assoc] at h₁ h₂
  have key := h₁.symm.trans h₂
  rw [F.sqIso_eq x t' t y sx (x ≫ t) rfl sx.symm, F.sqIso_eq z b' b v sb (z ≫ b) rfl sb.symm]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% key, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [Category.comp_id]

end CategoryTheory.ExchangeFormalism
