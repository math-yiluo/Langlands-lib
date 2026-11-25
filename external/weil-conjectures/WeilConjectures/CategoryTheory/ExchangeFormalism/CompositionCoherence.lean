/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Composition
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Identity
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Pasting

/-!
# Coherence of the composition isomorphisms in an exchange formalism

Let `F` be a `CategoryTheory.ExchangeFormalism`. The composition isomorphism
`F.shriek i₁ p₁ ⋙ F.shriek i₂ p₂ ≅ F.shriek i p` of a triangle of factorizations
(`CategoryTheory.ExchangeFormalism.compIso`) satisfies the following coherences:

- **associativity** (`CategoryTheory.ExchangeFormalism.compIso_assoc`): for composable morphisms
  `A ⟶ B ⟶ C ⟶ D` with factorizations `A ⟶[i_f] Z_f ⟶[p_f] B`, `B ⟶[i_g] P_g ⟶[p_g] C`,
  `C ⟶[i_h] P_h ⟶[p_h] D` and a staircase of squares
  ```
  Z_f --a--> W_fg --e--> V
  |p_f       |b          |u
  B --i_g--> P_g --c---> W_gh
             |p_g        |d
             C ---i_h--> P_h
  ```
  the two composition isomorphisms `Rf_! ⋙ Rg_! ⋙ Rh_! ≅ R(fgh)_!` built from the four triangles
  of the staircase agree;
- **unit laws** (`CategoryTheory.ExchangeFormalism.compIso_unitLeft_hom_app`,
  `CategoryTheory.ExchangeFormalism.compIso_unitRight_hom_app`): for the triangles with the
  trivial factorization `X ⟶[𝟙] X ⟶[𝟙] X` of an identity, the composition isomorphism is
  `(𝟙)_* (𝟙)_! ≅ 𝟭`;
- **proper triangles** (`CategoryTheory.ExchangeFormalism.compIso_ofProper_hom_app`): for the
  trivial factorizations `X ⟶[𝟙] X ⟶[f] Y`, `Y ⟶[𝟙] Y ⟶[g] S` and `X ⟶[𝟙] X ⟶[f ≫ g] S`, the
  composition isomorphism is the composition isomorphism `(f ≫ g)_* ≅ f_* ⋙ g_*` of the
  pushforwards.
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section Naturality

/-- Naturality of the inverse of the composition isomorphism `h_* ≅ f_* ⋙ g_*`, in a form
suitable for rewriting. -/
@[reassoc]
lemma pfComp'_inv_naturality {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    {M N : F.obj X} (φ : M ⟶ N) :
    (F.pfComp' f g h w).inv.app M ≫ (F.pf h).map φ =
      (F.pf g).map ((F.pf f).map φ) ≫ (F.pfComp' f g h w).inv.app N :=
  ((F.pfComp' f g h w).inv.naturality φ).symm

/-- Naturality of the exchange map `t_* ⋙ r_! ⟶ l_! ⋙ b_*`, in a form suitable for
rewriting. -/
@[reassoc]
lemma exchange_naturality {U' U Z' Z : 𝒞} (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    [Fact (𝒪 l)] [Fact (𝒪 r)] (w : t ≫ r = l ≫ b) [IsIso (F.baseChange t l r b w)]
    {M N : F.obj U'} (φ : M ⟶ N) :
    (F.sh r).map ((F.pf t).map φ) ≫ (F.exchange t l r b w).app N =
      (F.exchange t l r b w).app M ≫ (F.pf b).map ((F.sh l).map φ) :=
  (F.exchange t l r b w).naturality φ

end Naturality

section Assoc

variable {A B C D Zf Pg Ph Wfg Wgh V : 𝒞}
  (i_f : A ⟶ Zf) (p_f : Zf ⟶ B) (i_g : B ⟶ Pg) (p_g : Pg ⟶ C) (i_h : C ⟶ Ph) (p_h : Ph ⟶ D)
  (a : Zf ⟶ Wfg) (b : Wfg ⟶ Pg) (c : Pg ⟶ Wgh) (d : Wgh ⟶ Ph) (e : Wfg ⟶ V) (u : V ⟶ Wgh)
  (ifg : A ⟶ Wfg) (pfg : Wfg ⟶ C) (igh : B ⟶ Wgh) (pgh : Wgh ⟶ D) (ae : Zf ⟶ V) (ud : V ⟶ Ph)
  (i4 : A ⟶ V) (p4 : V ⟶ D)
  [Fact (𝒪 i_f)] [Fact (𝒪 i_g)] [Fact (𝒪 i_h)] [Fact (𝒪 a)] [Fact (𝒪 c)] [Fact (𝒪 e)]
  [Fact (𝒪 ifg)] [Fact (𝒪 igh)] [Fact (𝒪 ae)] [Fact (𝒪 i4)]
  (hifg : i_f ≫ a = ifg) (hpfg : b ≫ p_g = pfg) (high : i_g ≫ c = igh) (hpgh : d ≫ p_h = pgh)
  (hi4 : ifg ≫ e = i4) (hi4' : i_f ≫ ae = i4)
  (hp4 : ud ≫ p_h = p4) (hp4' : u ≫ pgh = p4)
  (S₁ : p_f ≫ i_g = a ≫ b) (S₂ : p_g ≫ i_h = c ≫ d) (S₃ : b ≫ c = e ≫ u)
  (S₃₂ : pfg ≫ i_h = e ≫ ud) (S₁₃ : p_f ≫ igh = ae ≫ u)

/-- **Associativity of the composition isomorphisms.** For a staircase of squares
```
Z_f --a--> W_fg --e--> V
|p_f       |b          |u
B --i_g--> P_g --c---> W_gh
           |p_g        |d
           C ---i_h--> P_h
```
with `S₁ : p_f ≫ i_g = a ≫ b`, `S₂ : p_g ≫ i_h = c ≫ d`, `S₃ : b ≫ c = e ≫ u`, the triangles
`T₁ = (i_f, p_f; i_g, p_g; a, b)` of `(f, g)`, `T₂ = (i_g, p_g; i_h, p_h; c, d)` of `(g, h)`,
`T₃ = (i_f ≫ a, b ≫ p_g; i_h, p_h; e, u ≫ d)` of `(f ≫ g, h)` and
`T₄ = (i_f, p_f; i_g ≫ c, d ≫ p_h; a ≫ e, u)` of `(f, g ≫ h)` give the same identification of
`F.shriek i4 p4` with `F.shriek i_f p_f ⋙ F.shriek i_g p_g ⋙ F.shriek i_h p_h`. -/
theorem compIso_assoc (hae : a ≫ e = ae) (hud : u ≫ d = ud)
    [IsIso (F.baseChange p_f a i_g b S₁)] [IsIso (F.exchange p_f a i_g b S₁)]
    [IsIso (F.baseChange p_g c i_h d S₂)] [IsIso (F.exchange p_g c i_h d S₂)]
    [IsIso (F.baseChange b e c u S₃)] [IsIso (F.exchange b e c u S₃)]
    [IsIso (F.baseChange pfg e i_h ud S₃₂)]
    [IsIso (F.exchange pfg e i_h ud S₃₂)]
    [IsIso (F.baseChange p_f ae igh u S₁₃)]
    [IsIso (F.exchange p_f ae igh u S₁₃)] (M : F.obj A) :
    (F.compIso (⟨Wfg, Ph, V, ifg, pfg, i_h, p_h, i4, p4, e, ud, hi4, hp4, S₃₂⟩ :
        ShriekTriangle 𝒪 A C D)).inv.app M ≫
      (F.shriek i_h p_h).map ((F.compIso (⟨Zf, Pg, Wfg, i_f, p_f, i_g, p_g, ifg, pfg, a, b,
        hifg, hpfg, S₁⟩ : ShriekTriangle 𝒪 A B C)).inv.app M) =
    (F.compIso (⟨Zf, Wgh, V, i_f, p_f, igh, pgh, i4, p4, ae, u, hi4', hp4', S₁₃⟩ :
        ShriekTriangle 𝒪 A B D)).inv.app M ≫
      (F.compIso (⟨Pg, Ph, Wgh, i_g, p_g, i_h, p_h, igh, pgh, c, d, high, hpgh, S₂⟩ :
        ShriekTriangle 𝒪 B C D)).inv.app ((F.shriek i_f p_f).obj M) := by
  simp only [← Iso.app_inv, ← Functor.mapIso_inv, ← Iso.trans_inv, Iso.inv_eq_inv]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [compIso_hom_app, compIso_hom_app, compIso_hom_app, compIso_hom_app]
  dsimp only [shriek, Functor.comp_obj, Functor.comp_map]
  have hP := congr_app (F.exchange_paste_horiz b p_g e c i_h u d pfg ud S₃ S₂ hpfg hud S₃₂)
    ((F.sh ifg).obj M)
  have hV := congr_app (F.exchange_paste_vert p_f b u a i_g e c ae igh S₁ S₃ hae high S₁₃)
    ((F.sh i_f).obj M)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.hComp, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_obj]
    at hP hV
  rw [hP, hV]
  simp only [Category.assoc]
  rw [F.pfComp'_inv_naturality_assoc d p_h pgh hpgh,
    F.pfComp'_assoc_inv_app u d p_h ud pgh p4 hud hpgh hp4 hp4']
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  refine congrArg (· ≫ _) (congrArg (F.pf p_h).map ?_)
  have hc₁ : (F.sh i_h).map ((F.pfComp' b p_g pfg hpfg).inv.app ((F.sh ifg).obj M)) ≫
      (F.sh i_h).map ((F.pfComp' b p_g pfg hpfg).hom.app ((F.sh ifg).obj M)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  have hc₂ : (F.pf d).map
      ((F.shComp' i_g c igh high).inv.app ((F.pf p_f).obj ((F.sh i_f).obj M))) ≫
      (F.pf d).map ((F.shComp' i_g c igh high).hom.app ((F.pf p_f).obj ((F.sh i_f).obj M))) =
        𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  have h₃ := congrArg (F.pf d).map
    (F.exchange_naturality b e c u S₃ ((F.shComp' i_f a ifg hifg).inv.app M))
  have h₄ := congrArg (fun φ ↦ (F.pf d).map ((F.pf u).map φ))
    (F.shComp'_assoc_inv_app i_f a e ifg ae i4 hifg hae hi4 hi4' M)
  simp only [Functor.map_comp] at h₃ h₄
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc₁, reassoc_of% hc₂, F.pfComp'_inv_naturality u d ud hud,
    F.exchange_naturality_assoc p_g c i_h d S₂, F.exchange_naturality_assoc p_g c i_h d S₂,
    reassoc_of% h₃, reassoc_of% h₄]

end Assoc

section UnitHelpers

variable [𝒪.ContainsIdentities] {X Y : 𝒞}

/-- The inverse of the composition isomorphism `j_! ≅ (𝟙)_! ⋙ j_!`, objectwise. -/
lemma shComp'_id_left_inv_app (j : X ⟶ Y) [Fact (𝒪 j)] (h : 𝟙 X ≫ j = j) (M : F.obj X) :
    (F.shComp' (𝟙 X) j j h).inv.app M = (F.sh j).map ((F.shId X).hom.app M) := by
  have := congr_app (F.shComp'_id_left j) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    NatTrans.id_app, Functor.id_obj, Functor.comp_obj, Category.comp_id] at this
  rw [← cancel_epi ((F.shComp' (𝟙 X) j j h).hom.app M), Iso.hom_inv_id_app]
  exact this.symm

/-- The inverse of the composition isomorphism `j_! ≅ j_! ⋙ (𝟙)_!`, objectwise. -/
lemma shComp'_id_right_inv_app (j : X ⟶ Y) [Fact (𝒪 j)] (h : j ≫ 𝟙 Y = j) (M : F.obj X) :
    (F.shComp' j (𝟙 Y) j h).inv.app M = (F.shId Y).hom.app ((F.sh j).obj M) := by
  have := congr_app (F.shComp'_id_right j) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app, Functor.id_obj, Functor.comp_obj, Category.comp_id] at this
  rw [← cancel_epi ((F.shComp' j (𝟙 Y) j h).hom.app M), Iso.hom_inv_id_app]
  exact this.symm

omit [𝒪.ContainsIdentities] in
/-- The exchange map of the square `𝟙 ≫ j = j ≫ 𝟙`, objectwise. -/
lemma exchange_id_horiz_app (j : X ⟶ Y) [Fact (𝒪 j)] (w : 𝟙 X ≫ j = j ≫ 𝟙 Y)
    [IsIso (F.baseChange (𝟙 X) j j (𝟙 Y) w)] (N : F.obj X) :
    (F.exchange (𝟙 X) j j (𝟙 Y) w).app N =
      (F.sh j).map ((F.pfId X).hom.app N) ≫ (F.pfId Y).inv.app ((F.sh j).obj N) := by
  rw [F.exchange_id_horiz j w]
  simp

/-- The exchange map of the square `g ≫ 𝟙 = 𝟙 ≫ g`, objectwise. -/
lemma exchange_id_vert_app (g : X ⟶ Y) (w : g ≫ 𝟙 Y = 𝟙 X ≫ g)
    [IsIso (F.baseChange g (𝟙 X) (𝟙 Y) g w)] (N : F.obj X) :
    (F.exchange g (𝟙 X) (𝟙 Y) g w).app N =
      (F.shId Y).hom.app ((F.pf g).obj N) ≫ (F.pf g).map ((F.shId X).inv.app N) := by
  rw [F.exchange_id_vert g w]
  simp

end UnitHelpers

section Unit

variable [𝒪.ContainsIdentities] {X Y Z : 𝒞} (i : X ⟶ Z) (p : Z ⟶ Y) [Fact (𝒪 i)]

/-- **The left unit law of the composition isomorphisms.** For the triangle
`((𝟙, 𝟙); (i, p); i, 𝟙)` of `(𝟙 X, f)`, with `X ⟶[i] Z ⟶[p] Y` a factorization of `f`, the
composition isomorphism `F.shriek (𝟙 X) (𝟙 X) ⋙ F.shriek i p ≅ F.shriek i p` is induced by
`(𝟙 X)_* (𝟙 X)_! ≅ 𝟭`. -/
theorem compIso_unitLeft_hom_app (w : 𝟙 X ≫ i = i ≫ 𝟙 Z)
    [IsIso (F.baseChange (𝟙 X) i i (𝟙 Z) w)]
    [IsIso (F.exchange (𝟙 X) i i (𝟙 Z) w)] (M : F.obj X) :
    (F.compIso (⟨X, Z, Z, 𝟙 X, 𝟙 X, i, p, i, p, i, 𝟙 Z, Category.id_comp i,
        Category.id_comp p, w⟩ : ShriekTriangle 𝒪 X X Y)).hom.app M =
      (F.shriek i p).map ((F.pf (𝟙 X)).map ((F.shId X).hom.app M) ≫ (F.pfId X).hom.app M) := by
  rw [compIso_hom_app]
  dsimp only
  rw [exchange_id_horiz_app, shComp'_id_left_inv_app, pfComp'_id_left_inv_app]
  have h := (F.pfId Z).inv.naturality ((F.sh i).map ((F.shId X).hom.app M))
  dsimp only [Functor.id_obj, Functor.id_map] at h
  simp only [shriek, Functor.comp_map, Category.assoc, ← h, ← Functor.map_comp,
    Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id]
  rw [(F.pfId X).hom.naturality, Functor.id_map, Functor.map_comp, Functor.map_comp]

/-- **The right unit law of the composition isomorphisms.** For the triangle
`((i, p); (𝟙, 𝟙); 𝟙, p)` of `(f, 𝟙 Y)`, with `X ⟶[i] Z ⟶[p] Y` a factorization of `f`, the
composition isomorphism `F.shriek i p ⋙ F.shriek (𝟙 Y) (𝟙 Y) ≅ F.shriek i p` is induced by
`(𝟙 Y)_* (𝟙 Y)_! ≅ 𝟭`. -/
theorem compIso_unitRight_hom_app (w : p ≫ 𝟙 Y = 𝟙 Z ≫ p)
    [IsIso (F.baseChange p (𝟙 Z) (𝟙 Y) p w)]
    [IsIso (F.exchange p (𝟙 Z) (𝟙 Y) p w)] (M : F.obj X) :
    (F.compIso (⟨Z, Y, Z, i, p, 𝟙 Y, 𝟙 Y, i, p, 𝟙 Z, p, Category.comp_id i,
        Category.comp_id p, w⟩ : ShriekTriangle 𝒪 X Y Y)).hom.app M =
      (F.pf (𝟙 Y)).map ((F.shId Y).hom.app ((F.shriek i p).obj M)) ≫
        (F.pfId Y).hom.app ((F.shriek i p).obj M) := by
  rw [compIso_hom_app]
  dsimp only
  rw [exchange_id_vert_app, shComp'_id_right_inv_app, pfComp'_id_right_inv_app]
  simp only [shriek, Functor.comp_obj, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.id_obj, Category.comp_id, Functor.map_id]

end Unit

section Proper

variable [𝒪.ContainsIdentities] {X Y S : 𝒞} (f : X ⟶ Y) (g : Y ⟶ S) (fg : X ⟶ S)
  (hfg : f ≫ g = fg)

/-- **The composition isomorphism of trivial factorizations.** For the triangle
`((𝟙, f); (𝟙, g); 𝟙, f)` of `(f, g)` with the trivial factorizations `X ⟶[𝟙] X ⟶[f] Y`,
`Y ⟶[𝟙] Y ⟶[g] S` and `X ⟶[𝟙] X ⟶[f ≫ g] S`, the composition isomorphism is, through
`(𝟙 Y)_! ≅ 𝟭`, the composition isomorphism `(f ≫ g)_* ≅ f_* ⋙ g_*` of the pushforwards. -/
theorem compIso_ofProper_hom_app (w : f ≫ 𝟙 Y = 𝟙 X ≫ f)
    [IsIso (F.baseChange f (𝟙 X) (𝟙 Y) f w)]
    [IsIso (F.exchange f (𝟙 X) (𝟙 Y) f w)] (M : F.obj X) :
    (F.compIso (⟨X, Y, X, 𝟙 X, f, 𝟙 Y, g, 𝟙 X, fg, 𝟙 X, f, Category.id_comp _, hfg, w⟩ :
        ShriekTriangle 𝒪 X Y S)).hom.app M =
      (F.pf g).map ((F.shId Y).hom.app ((F.pf f).obj ((F.sh (𝟙 X)).obj M))) ≫
        (F.pfComp' f g fg hfg).inv.app ((F.sh (𝟙 X)).obj M) := by
  rw [compIso_hom_app]
  dsimp only
  rw [exchange_id_vert_app, shComp'_id_right_inv_app]
  simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.id_obj, Category.comp_id, Functor.map_id]

end Proper

end CategoryTheory.ExchangeFormalism
