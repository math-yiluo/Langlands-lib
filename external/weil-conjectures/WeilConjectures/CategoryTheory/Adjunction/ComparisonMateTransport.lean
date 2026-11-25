/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transport of mates along comparison functors

Given two squares of left adjoints related by comparison functors, the mates of the two squares
are related by the comparison functors (`CategoryTheory.mateEquiv_app_comparison_transport`).
A commutative cube of comparison squares stays commutative after replacing its edges by
isomorphic functors (`CategoryTheory.cube_conjugation`).
-/

@[expose] public section

open CategoryTheory

section MateTransport

variable {E₀ E₁ E₂ E₃ P₀ P₁ P₂ P₃ : Type*}
  [Category E₀] [Category E₁] [Category E₂] [Category E₃]
  [Category P₀] [Category P₁] [Category P₂] [Category P₃]
  {l : E₀ ⥤ E₁} {r : E₁ ⥤ E₀} {l' : E₂ ⥤ E₃} {r' : E₃ ⥤ E₂}
  {p : P₀ ⥤ P₁} {s : P₁ ⥤ P₀} {p' : P₂ ⥤ P₃} {s' : P₃ ⥤ P₂}
  {g : E₀ ⥤ E₂} {h : E₁ ⥤ E₃} {q : P₀ ⥤ P₂} {t : P₁ ⥤ P₃}
  {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} {A₂ : E₂ ⥤ P₂} {A₃ : E₃ ⥤ P₃}

/-- Transport of mates along comparison functors. Consider two squares of left adjoints
```
        g                      q
   E₀ ────▶ E₂            P₀ ────▶ P₂
   │        │             │        │
  l│   θ    │l'          p│   ϑ    │p'
   ▼        ▼             ▼        ▼
   E₁ ────▶ E₃            P₁ ────▶ P₃
        h                      t
```
with `e : l ⊣ r`, `e' : l' ⊣ r'`, `d : p ⊣ s`, `d' : p' ⊣ s'`, and comparison functors
`Aᵢ : Eᵢ ⥤ Pᵢ` together with isomorphisms `a, a', c, c'` between the left adjoints and
families of maps `b, b'` between the right adjoints (not required to be natural). If `b, b'`
are compatible with the counits (`hb`, `hb'`) and the cube of left adjoints commutes (`hsq`),
then the mate of `θ`, conjugated by the comparison functors, is the mate of `ϑ`. -/
theorem CategoryTheory.mateEquiv_app_comparison_transport (e : l ⊣ r) (e' : l' ⊣ r')
    (d : p ⊣ s) (d' : p' ⊣ s') (a : l ⋙ A₁ ≅ A₀ ⋙ p) (a' : l' ⋙ A₃ ≅ A₂ ⋙ p')
    (c : g ⋙ A₂ ≅ A₀ ⋙ q) (c' : h ⋙ A₃ ≅ A₁ ⋙ t)
    (b : ∀ K, A₀.obj (r.obj K) ⟶ s.obj (A₁.obj K))
    (b' : ∀ K, A₂.obj (r'.obj K) ⟶ s'.obj (A₃.obj K))
    (θ : g ⋙ l' ⟶ l ⋙ h) (ϑ : q ⋙ p' ⟶ p ⋙ t)
    (hb : ∀ K, a.hom.app (r.obj K) ≫ p.map (b K) ≫ d.counit.app (A₁.obj K) =
      A₁.map (e.counit.app K))
    (hb' : ∀ K, a'.hom.app (r'.obj K) ≫ p'.map (b' K) ≫ d'.counit.app (A₃.obj K) =
      A₃.map (e'.counit.app K))
    (hsq : ∀ M, A₃.map (θ.app M) ≫ c'.hom.app (l.obj M) ≫ t.map (a.hom.app M) =
      a'.hom.app (g.obj M) ≫ p'.map (c.hom.app M) ≫ ϑ.app (A₀.obj M)) (K : E₁) :
    A₂.map ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).app K) ≫ b' (h.obj K) ≫
      s'.map (c'.hom.app K) =
    c.hom.app (r.obj K) ≫ q.map (b K) ≫
      (mateEquiv d d' (TwoSquare.mk _ _ _ _ ϑ)).app (A₁.obj K) := by
  apply (d'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (a'.hom.app (g.obj (r.obj K)))).1
  have hn := a'.hom.naturality ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).app K)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [d'.counit_naturality, reassoc_of% hb']
  rw [← A₃.map_comp_assoc, mateEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hn' := c'.hom.naturality (e.counit.app K)
  simp only [Functor.comp_map] at hn'
  erw [hn', mateEquiv_counit]
  have ht := ϑ.naturality (b K)
  simp only [Functor.comp_map] at ht
  erw [reassoc_of% ht, ← reassoc_of% hsq]
  simp only [← Functor.map_comp, hb, TwoSquare.mk, Functor.comp_obj]

end MateTransport

section CubeConjugation

variable {E₀ E₁ E₂ E₃ P₀ P₁ P₂ P₃ : Type*}
  [Category E₀] [Category E₁] [Category E₂] [Category E₃]
  [Category P₀] [Category P₁] [Category P₂] [Category P₃]
  {l lD : E₀ ⥤ E₁} {l' l'D : E₂ ⥤ E₃} {g gD : E₀ ⥤ E₂} {h hD : E₁ ⥤ E₃}
  {p pD : P₀ ⥤ P₁} {p' p'D : P₂ ⥤ P₃} {q qD : P₀ ⥤ P₂} {t tD : P₁ ⥤ P₃}
  {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} {A₂ : E₂ ⥤ P₂} {A₃ : E₃ ⥤ P₃}

/-- A commutative cube of comparison squares stays commutative after replacing each of the
eight edge functors `lD, l'D, gD, hD, pD, p'D, qD, tD` by an isomorphic functor and
conjugating the six faces accordingly. -/
theorem CategoryTheory.cube_conjugation (jl : l ≅ lD) (jl' : l' ≅ l'D) (jg : g ≅ gD)
    (jh : h ≅ hD) (kp : p ≅ pD) (kp' : p' ≅ p'D) (kq : q ≅ qD) (kt : t ≅ tD)
    (Sl : lD ⋙ A₁ ≅ A₀ ⋙ pD) (Sl' : l'D ⋙ A₃ ≅ A₂ ⋙ p'D) (Sg : gD ⋙ A₂ ≅ A₀ ⋙ qD)
    (Sh : hD ⋙ A₃ ≅ A₁ ⋙ tD) (θD : gD ⋙ l'D ≅ lD ⋙ hD) (ϑD : qD ⋙ p'D ≅ pD ⋙ tD)
    (hcube : ∀ M, Sl'.hom.app (gD.obj M) ≫ p'D.map (Sg.hom.app M) ≫ ϑD.hom.app (A₀.obj M) =
      A₃.map (θD.hom.app M) ≫ Sh.hom.app (lD.obj M) ≫ tD.map (Sl.hom.app M)) (M : E₀) :
    A₃.map (((Functor.isoWhiskerLeft g jl' ≪≫ Functor.isoWhiskerRight jg l'D) ≪≫ θD ≪≫
        (Functor.isoWhiskerLeft l jh ≪≫ Functor.isoWhiskerRight jl hD).symm).hom.app M) ≫
      (Functor.isoWhiskerRight jh A₃ ≪≫ Sh ≪≫ Functor.isoWhiskerLeft A₁ kt.symm).hom.app
        (l.obj M) ≫
      t.map ((Functor.isoWhiskerRight jl A₁ ≪≫ Sl ≪≫
        Functor.isoWhiskerLeft A₀ kp.symm).hom.app M) =
    (Functor.isoWhiskerRight jl' A₃ ≪≫ Sl' ≪≫ Functor.isoWhiskerLeft A₂ kp'.symm).hom.app
        (g.obj M) ≫
      p'.map ((Functor.isoWhiskerRight jg A₂ ≪≫ Sg ≪≫
        Functor.isoWhiskerLeft A₀ kq.symm).hom.app M) ≫
      ((Functor.isoWhiskerLeft q kp' ≪≫ Functor.isoWhiskerRight kq p'D) ≪≫ ϑD ≪≫
        (Functor.isoWhiskerLeft p kt ≪≫ Functor.isoWhiskerRight kp tD).symm).hom.app
        (A₀.obj M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc, Functor.comp_obj]
  have h₁ := Sh.hom.naturality (jl.inv.app M)
  have h₂ := Sl'.hom.naturality (jg.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  rw [← A₃.map_comp_assoc (jh.inv.app (l.obj M)), Iso.inv_hom_id_app, A₃.map_id,
    Category.id_comp, reassoc_of% h₁, ← kt.inv.naturality_assoc, ← kt.inv.naturality_assoc,
    ← kt.inv.naturality, ← tD.map_comp_assoc, ← A₁.map_comp, Iso.inv_hom_id_app,
    A₁.map_id, tD.map_id, Category.id_comp]
  rw [← kp'.inv.naturality_assoc, ← kp'.inv.naturality_assoc, ← kp'.inv.naturality_assoc,
    Iso.inv_hom_id_app_assoc, ← p'D.map_comp_assoc (kq.inv.app (A₀.obj M)),
    Iso.inv_hom_id_app, p'D.map_id, Category.id_comp, ← reassoc_of% h₂, reassoc_of% (hcube M)]

end CubeConjugation
