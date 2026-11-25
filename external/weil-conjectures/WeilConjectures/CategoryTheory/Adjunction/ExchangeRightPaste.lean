/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Exchange morphisms as mates, and their pasting law

The exchange morphism `CategoryTheory.Adjunction.exchangeRight af af' θ` of a commutative square
of left adjoints is the mate of `θ.hom` (`CategoryTheory.Adjunction.exchangeRight_eq_mateEquiv`),
hence an isomorphism when the horizontal functors are equivalences
(`CategoryTheory.Adjunction.isIso_exchangeRight_of_isEquivalence`), and the exchange morphisms of
two horizontally pasted squares paste (`CategoryTheory.Adjunction.exchangeRight_app_paste`), so
that the outer one is invertible at an object exactly when the first one is, after applying the
horizontal functor of the second square, provided the second one is invertible
(`CategoryTheory.Adjunction.isIso_exchangeRight_app_paste_iff`).

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

section ExchangeRight

variable {A B A' B' A'' B'' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Category* A''] [Category* B''] {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
  {Lf'' : B'' ⥤ A''} {Rf'' : A'' ⥤ B''}

/-- The exchange morphism `exchangeRight af af' θ` is the mate of `θ.hom`. -/
lemma exchangeRight_eq_mateEquiv {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    exchangeRight af af' θ = (mateEquiv af af' (TwoSquare.mk _ _ _ _ θ.hom)) := by
  ext K
  rw [exchangeRight_app]
  simp [mateEquiv]

/-- The exchange morphism of a natural isomorphism is an isomorphism when the horizontal functors
are equivalences. -/
lemma isIso_exchangeRight_of_isEquivalence {G : B ⥤ B'} {G' : A ⥤ A'} [G.IsEquivalence]
    [G'.IsEquivalence] (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    IsIso (exchangeRight af af' θ) := by
  rw [exchangeRight_eq_mateEquiv]
  exact isIso_mateEquiv_of_isEquivalence af af' _

/-- **Pasting law of exchange morphisms.** Let `θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁'` and
`θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂'` be comparisons of two horizontally adjacent squares, and
`θ : G ⋙ Lf'' ≅ Lf ⋙ G'` one of the outer square, compatible with `θ₁` and `θ₂` through
isomorphisms `c : G ≅ G₁ ⋙ G₂` and `c' : G' ≅ G₁' ⋙ G₂'`. Then the exchange morphism of `θ` is
the pasting of those of `θ₁` and `θ₂`, through `c` and `c'`. The squares are
```
B --G₁--> B' --G₂--> B''
|Lf        |Lf'       |Lf''
v          v           v
A --G₁'-> A' --G₂'-> A''
```
with right adjoints `Rf`, `Rf'`, `Rf''` going up. -/
lemma exchangeRight_app_paste {G₁ : B ⥤ B'} {G₁' : A ⥤ A'} {G₂ : B' ⥤ B''} {G₂' : A' ⥤ A''}
    {G : B ⥤ B''} {G' : A ⥤ A''} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (af'' : Lf'' ⊣ Rf'')
    (θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁') (θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂') (θ : G ⋙ Lf'' ≅ Lf ⋙ G')
    (c : G ≅ G₁ ⋙ G₂) (c' : G' ≅ G₁' ⋙ G₂')
    (h : ∀ N : B, Lf''.map (c.hom.app N) ≫ θ₂.hom.app (G₁.obj N) ≫ G₂'.map (θ₁.hom.app N) =
      θ.hom.app N ≫ c'.hom.app (Lf.obj N)) (K : A) :
    c.hom.app (Rf.obj K) ≫ G₂.map ((exchangeRight af af' θ₁).app K) ≫
        (exchangeRight af' af'' θ₂).app (G₁'.obj K) =
      (exchangeRight af af'' θ).app K ≫ Rf''.map (c'.hom.app K) := by
  have h₁ : Lf'.map ((exchangeRight af af' θ₁).app K) ≫ af'.counit.app (G₁'.obj K) =
      θ₁.hom.app (Rf.obj K) ≫ G₁'.map (af.counit.app K) := by
    have h := (af'.homEquiv _ _).symm_apply_apply
      (θ₁.hom.app (Rf.obj K) ≫ G₁'.map (af.counit.app K))
    rw [homEquiv_counit, homEquiv_unit] at h
    rw [exchangeRight_app, ← Rf'.map_comp]
    exact h
  have hη := af''.unit.naturality
    (c.hom.app (Rf.obj K) ≫ G₂.map ((exchangeRight af af' θ₁).app K))
  have hθ := θ₂.hom.naturality ((exchangeRight af af' θ₁).app K)
  have hc := c'.hom.naturality (af.counit.app K)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hη hθ hc
  rw [exchangeRight_app af' af'' θ₂, exchangeRight_app af af'' θ, ← Category.assoc,
    ← Category.assoc, hη, Category.assoc, ← Rf''.map_comp, ← Rf''.map_comp, ← Rf''.map_comp,
    Lf''.map_comp, Category.assoc, reassoc_of% hθ, ← G₂'.map_comp, h₁, G₂'.map_comp,
    reassoc_of% h, ← hc]
  simp only [Functor.map_comp, Category.assoc]

/-- **Pointwise two-out-of-three for pasted exchange morphisms**: in the situation of
`CategoryTheory.Adjunction.exchangeRight_app_paste`, with the two pasted squares
```
B --G₁--> B' --G₂--> B''
|Lf        |Lf'       |Lf''
v          v           v
A --G₁'-> A' --G₂'-> A''
```
if the exchange morphism of the second square (`θ₂`) is invertible, then the exchange morphism
of the outer square (`θ`) is invertible at `K` if and only if the image under `G₂` of the exchange
morphism of the first square (`θ₁`) at `K` is invertible. -/
lemma isIso_exchangeRight_app_paste_iff {G₁ : B ⥤ B'} {G₁' : A ⥤ A'} {G₂ : B' ⥤ B''}
    {G₂' : A' ⥤ A''} {G : B ⥤ B''} {G' : A ⥤ A''} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (af'' : Lf'' ⊣ Rf'') (θ₁ : G₁ ⋙ Lf' ≅ Lf ⋙ G₁') (θ₂ : G₂ ⋙ Lf'' ≅ Lf' ⋙ G₂')
    (θ : G ⋙ Lf'' ≅ Lf ⋙ G') (c : G ≅ G₁ ⋙ G₂) (c' : G' ≅ G₁' ⋙ G₂')
    (h : ∀ N : B, Lf''.map (c.hom.app N) ≫ θ₂.hom.app (G₁.obj N) ≫ G₂'.map (θ₁.hom.app N) =
      θ.hom.app N ≫ c'.hom.app (Lf.obj N)) (hθ₂ : IsIso (exchangeRight af' af'' θ₂)) (K : A) :
    IsIso ((exchangeRight af af'' θ).app K) ↔
      IsIso (G₂.map ((exchangeRight af af' θ₁).app K)) := by
  have e := exchangeRight_app_paste af af' af'' θ₁ θ₂ θ c c' h K
  constructor
  · intro _
    have : IsIso (c.hom.app (Rf.obj K) ≫ G₂.map ((exchangeRight af af' θ₁).app K) ≫
        (exchangeRight af' af'' θ₂).app (G₁'.obj K)) := by
      rw [e]
      infer_instance
    have := IsIso.of_isIso_comp_left (c.hom.app (Rf.obj K))
      (G₂.map ((exchangeRight af af' θ₁).app K) ≫ (exchangeRight af' af'' θ₂).app (G₁'.obj K))
    exact IsIso.of_isIso_comp_right _ ((exchangeRight af' af'' θ₂).app (G₁'.obj K))
  · intro _
    have : IsIso ((exchangeRight af af'' θ).app K ≫ Rf''.map (c'.hom.app K)) := by
      rw [← e]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Rf''.map (c'.hom.app K))

end ExchangeRight

end CategoryTheory.Adjunction
