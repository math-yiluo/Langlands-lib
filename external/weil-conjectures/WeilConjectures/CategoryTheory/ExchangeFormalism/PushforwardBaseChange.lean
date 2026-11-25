/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Cube

/-!
# The base change maps of the pushforwards in an exchange formalism

Let `F` be a `CategoryTheory.ExchangeFormalism`. For a commutative square
```
U' --t--> U
|l        |r
Z' --b--> Z
```
the *base change map of the pushforwards* `b^* r_* ⟶ l_* t^*` is the mate of the square
isomorphism `r^* ⋙ t^* ≅ b^* ⋙ l^*` (`CategoryTheory.ExchangeFormalism.pfBaseChange`). This file
proves its identity and pasting laws, and its compatibility with the exchange maps on a
commutative cube (`CategoryTheory.ExchangeFormalism.exchange_pfBaseChange_cube`).
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism

open TwoSquare

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section PushforwardBaseChange

variable {U' U Z' Z : 𝒞}

/-- **The base change map of the pushforwards**: for a commutative square `t ≫ r = l ≫ b`, the
map `r_* ⋙ b^* ⟶ t^* ⋙ l_*`, i.e. `b^* r_* ⟶ l_* t^*`, the mate of the inverse of
`ExchangeFormalism.sqIso` under the adjunctions `r^* ⊣ r_*` and `l^* ⊣ l_*`.
```
U' --t--> U
|l        |r
Z' --b--> Z
```
-/
def pfBaseChange (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) (w : t ≫ r = l ≫ b) :
    TwoSquare (F.pf r) (F.pb t) (F.pb b) (F.pf l) :=
  mateEquiv (F.adj r) (F.adj l) (F.sqIso t l r b w).inv

/-- The inverse of the square isomorphism of the square `𝟙 ≫ j = j ≫ 𝟙`. -/
lemma sqIso_id_horiz_inv {X Y : 𝒞} (j : X ⟶ Y) (w : 𝟙 X ≫ j = j ≫ 𝟙 Y) :
    (F.sqIso (𝟙 X) j j (𝟙 Y) w).inv =
      ((TwoSquare.mk (𝟭 _) (F.pb j) (F.pb j) (𝟭 _)
        ((Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)).whiskerTop
          (F.pbId Y).hom).whiskerBottom (F.pbId X).inv := by
  apply Iso.inv_ext
  rw [sqIso_id_horiz_hom]
  ext M
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.id_comp, Category.assoc, NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

/-- The base change map of the pushforwards of the square `𝟙 ≫ j = j ≫ 𝟙` is the identity, up
to `(𝟙)^* ≅ 𝟭`. -/
lemma pfBaseChange_id_horiz {X Y : 𝒞} (j : X ⟶ Y) (w : 𝟙 X ≫ j = j ≫ 𝟙 Y) :
    F.pfBaseChange (𝟙 X) j j (𝟙 Y) w =
      ((TwoSquare.mk (F.pf j) (𝟭 _) (𝟭 _) (F.pf j)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerRight
          (F.pbId Y).hom).whiskerLeft (F.pbId X).inv := by
  rw [pfBaseChange, sqIso_id_horiz_inv, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_unitors]

/-- **Horizontal pasting of the inverses of square isomorphisms.**
```
U'' --t₁--> U' --t₂--> U
|l          |m          |r
Z'' --b₁--> Z' --b₂--> Z
```
-/
lemma sqIso_inv_paste_horiz {U'' U' U Z'' Z' Z : 𝒞} (t₁ : U'' ⟶ U')
    (t₂ : U' ⟶ U) (l : U'' ⟶ Z'') (m : U' ⟶ Z') (r : U ⟶ Z) (b₁ : Z'' ⟶ Z') (b₂ : Z' ⟶ Z)
    (t : U'' ⟶ U) (b : Z'' ⟶ Z) (w₁ : t₁ ≫ m = l ≫ b₁) (w₂ : t₂ ≫ r = m ≫ b₂)
    (ht : t₁ ≫ t₂ = t) (hb : b₁ ≫ b₂ = b) (w : t ≫ r = l ≫ b) :
    (F.sqIso t l r b w).inv =
      ((TwoSquare.mk _ _ _ _ (F.sqIso t₂ m r b₂ w₂).inv ≫ₕ
        TwoSquare.mk _ _ _ _ (F.sqIso t₁ l m b₁ w₁).inv).whiskerTop
          (F.pbComp' b₁ b₂ b hb).hom).whiskerBottom (F.pbComp' t₁ t₂ t ht).inv := by
  apply Iso.inv_ext
  ext M
  rw [NatTrans.comp_app, F.sqIso_hom_app_paste_horiz t₁ t₂ l m r b₁ b₂ t b w₁ w₂ ht hb w M]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc,
    NatTrans.id_app, Functor.comp_obj]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app]

/-- **Horizontal pasting of base change maps of the pushforwards.**
```
U'' --t₁--> U' --t₂--> U
|l          |m          |r
Z'' --b₁--> Z' --b₂--> Z
```
-/
lemma pfBaseChange_paste_horiz {U'' U' U Z'' Z' Z : 𝒞} (t₁ : U'' ⟶ U')
    (t₂ : U' ⟶ U) (l : U'' ⟶ Z'') (m : U' ⟶ Z') (r : U ⟶ Z) (b₁ : Z'' ⟶ Z') (b₂ : Z' ⟶ Z)
    (t : U'' ⟶ U) (b : Z'' ⟶ Z) (w₁ : t₁ ≫ m = l ≫ b₁) (w₂ : t₂ ≫ r = m ≫ b₂)
    (ht : t₁ ≫ t₂ = t) (hb : b₁ ≫ b₂ = b) (w : t ≫ r = l ≫ b) :
    F.pfBaseChange t l r b w =
      ((F.pfBaseChange t₂ m r b₂ w₂ ≫ᵥ F.pfBaseChange t₁ l m b₁ w₁).whiskerRight
        (F.pbComp' b₁ b₂ b hb).hom).whiskerLeft (F.pbComp' t₁ t₂ t ht).inv := by
  rw [pfBaseChange, F.sqIso_inv_paste_horiz t₁ t₂ l m r b₁ b₂ t b w₁ w₂ ht hb w,
    mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp _ (F.adj m)]
  rfl

/-- **Vertical pasting of the inverses of square isomorphisms.**
```
U' --t--> U
|l₁       |r₁
W' --h--> W
|l₂       |r₂
Z' --b--> Z
```
-/
lemma sqIso_inv_paste_vert {U' U W' W Z' Z : 𝒞} (t : U' ⟶ U) (h : W' ⟶ W)
    (b : Z' ⟶ Z) (l₁ : U' ⟶ W') (r₁ : U ⟶ W) (l₂ : W' ⟶ Z') (r₂ : W ⟶ Z) (l : U' ⟶ Z')
    (r : U ⟶ Z) (w₁ : t ≫ r₁ = l₁ ≫ h) (w₂ : h ≫ r₂ = l₂ ≫ b) (hl : l₁ ≫ l₂ = l)
    (hr : r₁ ≫ r₂ = r) (w : t ≫ r = l ≫ b) :
    (F.sqIso t l r b w).inv =
      ((TwoSquare.mk _ _ _ _ (F.sqIso h l₂ r₂ b w₂).inv ≫ᵥ
        TwoSquare.mk _ _ _ _ (F.sqIso t l₁ r₁ h w₁).inv).whiskerLeft
          (F.pbComp' r₁ r₂ r hr).inv).whiskerRight (F.pbComp' l₁ l₂ l hl).hom := by
  apply Iso.inv_ext
  ext M
  rw [NatTrans.comp_app, F.sqIso_hom_app_paste_vert t h b l₁ r₁ l₂ r₂ l r w₁ w₂ hl hr w M]
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc, NatTrans.id_app,
    Functor.comp_obj]
  rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]

/-- **Vertical pasting of base change maps of the pushforwards.**
```
U' --t--> U
|l₁       |r₁
W' --h--> W
|l₂       |r₂
Z' --b--> Z
```
-/
lemma pfBaseChange_paste_vert {U' U W' W Z' Z : 𝒞} (t : U' ⟶ U) (h : W' ⟶ W)
    (b : Z' ⟶ Z) (l₁ : U' ⟶ W') (r₁ : U ⟶ W) (l₂ : W' ⟶ Z') (r₂ : W ⟶ Z) (l : U' ⟶ Z')
    (r : U ⟶ Z) (w₁ : t ≫ r₁ = l₁ ≫ h) (w₂ : h ≫ r₂ = l₂ ≫ b) (hl : l₁ ≫ l₂ = l)
    (hr : r₁ ≫ r₂ = r) (w : t ≫ r = l ≫ b) :
    F.pfBaseChange t l r b w =
      ((F.pfBaseChange t l₁ r₁ h w₁ ≫ₕ F.pfBaseChange h l₂ r₂ b w₂).whiskerTop
        (F.pfComp' r₁ r₂ r hr).hom).whiskerBottom (F.pfComp' l₁ l₂ l hl).inv := by
  have hP : conjugateEquiv (F.adj r) ((F.adj r₂).comp (F.adj r₁)) (F.pbComp' r₁ r₂ r hr).inv =
      (F.pfComp' r₁ r₂ r hr).hom := rfl
  have hP' : conjugateEquiv ((F.adj l₂).comp (F.adj l₁)) (F.adj l) (F.pbComp' l₁ l₂ l hl).hom =
      (F.pfComp' l₁ l₂ l hl).inv := rfl
  rw [pfBaseChange, F.sqIso_inv_paste_vert t h b l₁ r₁ l₂ r₂ l r w₁ w₂ hl hr w,
    mateEquiv_conjugateEquiv_vcomp _ ((F.adj l₂).comp (F.adj l₁)),
    conjugateEquiv_mateEquiv_vcomp _ ((F.adj r₂).comp (F.adj r₁)), mateEquiv_hcomp, hP, hP']
  rfl


end PushforwardBaseChange

section Cube

variable {U' U Z' Z V' V W' W : 𝒞}

/-- The base change map of the pushforwards, transposed along `l^* ⊣ l_*`: it is the inverse of
the square isomorphism followed by the counit of `r^* ⊣ r_*`. -/
@[reassoc]
lemma pfBaseChange_counit (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    (w : t ≫ r = l ≫ b) (M : F.obj U) :
    (F.pb l).map ((F.pfBaseChange t l r b w).app M) ≫
        (F.adj l).counit.app ((F.pb t).obj M) =
      (F.sqIso t l r b w).inv.app ((F.pf r).obj M) ≫ (F.pb t).map ((F.adj r).counit.app M) :=
  mateEquiv_counit (F.adj r) (F.adj l) _ M

/-- The exchange map, transposed along `b^* ⊣ b_*`: it is the inverse of the base change map
followed by the counit of `t^* ⊣ t_*`. -/
@[reassoc]
lemma exchange_counit (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [Fact (𝒪 l)]
    [Fact (𝒪 r)] (w : t ≫ r = l ≫ b) [IsIso (F.baseChange t l r b w)]
    (N : F.obj U') :
    (F.pb b).map ((F.exchange t l r b w).app N) ≫
        (F.adj b).counit.app ((F.sh l).obj N) =
      inv ((F.baseChange t l r b w).app ((F.pf t).obj N)) ≫
        (F.sh l).map ((F.adj t).counit.app N) := by
  have h := mateEquiv_counit (F.adj t) (F.adj b)
    (TwoSquare.mk _ _ _ _ (inv (F.baseChange t l r b w))) N
  simpa [exchange] using h

/-- **The exchange maps and the base change maps of the pushforwards on a cube.** For a
commutative cube with top face `t ≫ r = l ≫ b`, bottom face `t' ≫ r' = l' ≫ b'` (with `l`, `r`,
`l'`, `r'` open immersions) and connecting maps `x`, `y`, `z`, `v`
```
V' --t'--> V           U' --t--> U
|l'        |r'   ⟶     |l        |r
W' --b'--> W           Z' --b--> Z
```
the exchange maps of the top and bottom faces are intertwined by the base change maps of the
pushforwards of the faces `x ≫ t = t' ≫ y` and `z ≫ b = b' ≫ v` and the base change maps of the
extension by zero of the faces `x ≫ l = l' ≫ z` and `y ≫ r = r' ≫ v`. -/
lemma exchange_pfBaseChange_cube (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    (t' : V' ⟶ V) (l' : V' ⟶ W') (r' : V ⟶ W) (b' : W' ⟶ W) (x : V' ⟶ U') (y : V ⟶ U)
    (z : W' ⟶ Z') (v : W ⟶ Z) [Fact (𝒪 l)] [Fact (𝒪 r)] [Fact (𝒪 l')]
    [Fact (𝒪 r')] (w : t ≫ r = l ≫ b) (w' : t' ≫ r' = l' ≫ b') (sx : x ≫ t = t' ≫ y)
    (sl : x ≫ l = l' ≫ z) (sr : y ≫ r = r' ≫ v) (sb : z ≫ b = b' ≫ v)
    [IsIso (F.baseChange t l r b w)] [IsIso (F.baseChange t' l' r' b' w')]
    [IsIso (F.baseChange y r' r v sr)] (N : F.obj U') :
    inv ((F.baseChange y r' r v sr).app ((F.pf t).obj N)) ≫
        (F.sh r').map ((F.pfBaseChange x t' t y sx).app N) ≫
        (F.exchange t' l' r' b' w').app ((F.pb x).obj N) ≫
        (F.pf b').map ((F.baseChange x l' l z sl).app N) =
      (F.pb v).map ((F.exchange t l r b w).app N) ≫
        (F.pfBaseChange z b' b v sb).app ((F.sh l).obj N) := by
  -- the cube relation for the base change maps of the extension by zero, with inverses
  have hc := F.baseChange_cube t l r b t' l' r' b' x y z v w w' sx sl sr sb ((F.pf t).obj N)
  have hc' : (F.sh l').map ((F.sqIso x t' t y sx).inv.app ((F.pf t).obj N)) ≫
      (F.baseChange x l' l z sl).app ((F.pb t).obj ((F.pf t).obj N)) =
      (F.baseChange t' l' r' b' w').app ((F.pb y).obj ((F.pf t).obj N)) ≫
        (F.pb b').map ((F.baseChange y r' r v sr).app ((F.pf t).obj N)) ≫
        (F.sqIso z b' b v sb).inv.app ((F.sh r).obj ((F.pf t).obj N)) ≫
        (F.pb z).map (inv ((F.baseChange t l r b w).app ((F.pf t).obj N))) := by
    rw [← reassoc_of% hc]
    simp
  have hΞ : (F.pb b').map (inv ((F.baseChange y r' r v sr).app ((F.pf t).obj N))) ≫
      inv ((F.baseChange t' l' r' b' w').app ((F.pb y).obj ((F.pf t).obj N))) ≫
      (F.sh l').map ((F.sqIso x t' t y sx).inv.app ((F.pf t).obj N)) ≫
      (F.baseChange x l' l z sl).app ((F.pb t).obj ((F.pf t).obj N)) =
      (F.sqIso z b' b v sb).inv.app ((F.sh r).obj ((F.pf t).obj N)) ≫
        (F.pb z).map (inv ((F.baseChange t l r b w).app ((F.pf t).obj N))) := by
    rw [hc']
    simp
  -- transpose along `b'^* ⊣ b'_*`
  apply ((F.adj b').homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hβ' := (inv (F.baseChange t' l' r' b' w')).naturality
    ((F.pfBaseChange x t' t y sx).app N)
  have hγ := (F.baseChange x l' l z sl).naturality ((F.adj t).counit.app N)
  have hs := (F.sqIso z b' b v sb).inv.naturality ((F.exchange t l r b w).app N)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, NatIso.isIso_inv_app]
    at hβ' hγ hs
  erw [(F.adj b').counit_naturality]
  rw [F.exchange_counit_assoc t' l' r' b' w', reassoc_of% hβ',
    ← Functor.map_comp_assoc (F.sh l'), F.pfBaseChange_counit x t' t y sx, Functor.map_comp,
    Category.assoc, hγ]
  erw [F.pfBaseChange_counit z b' b v sb]
  rw [reassoc_of% hs, ← Functor.map_comp (F.pb z), F.exchange_counit t l r b w,
    Functor.map_comp, reassoc_of% hΞ]

end Cube

section IdVert

/-- The base change map of the pushforwards of the square `g ≫ 𝟙 = 𝟙 ≫ g` is the identity, up
to `(𝟙)_* ≅ 𝟭`. -/
lemma pfBaseChange_id_vert_app {X Y : 𝒞} (g : X ⟶ Y) (w : g ≫ 𝟙 Y = 𝟙 X ≫ g) (M : F.obj Y) :
    (F.pfBaseChange g (𝟙 X) (𝟙 Y) g w).app M ≫
        (F.pfId X).hom.app ((F.pb g).obj M) =
      (F.pb g).map ((F.pfId Y).hom.app M) := by
  have hId : ∀ {Z : 𝒞} (N : F.obj Z), (F.pfId Z).hom.app N =
      (F.pbId Z).inv.app ((F.pf (𝟙 Z)).obj N) ≫ (F.adj (𝟙 Z)).counit.app N := by
    intro Z N
    simp [pfId_hom]
  have hc := F.pfBaseChange_counit g (𝟙 X) (𝟙 Y) g w M
  have hs : (F.sqIso g (𝟙 X) (𝟙 Y) g w).inv.app ((F.pf (𝟙 Y)).obj M) =
      (F.pbId X).hom.app ((F.pb g).obj ((F.pf (𝟙 Y)).obj M)) ≫
        (F.pb g).map ((F.pbId Y).inv.app ((F.pf (𝟙 Y)).obj M)) := by
    rw [← cancel_epi ((F.sqIso g (𝟙 X) (𝟙 Y) g w).hom.app ((F.pf (𝟙 Y)).obj M)),
      Iso.hom_inv_id_app, F.sqIso_id_vert_hom]
    simp [← Functor.map_comp]
  rw [hId, hId]
  have hn := (F.pbId X).inv.naturality ((F.pfBaseChange g (𝟙 X) (𝟙 Y) g w).app M)
  simp only [Functor.id_map] at hn
  rw [reassoc_of% hn, hc, hs]
  simp [← Functor.map_comp]

end IdVert

end CategoryTheory.ExchangeFormalism
