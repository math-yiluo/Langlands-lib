/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport

/-!

# The restriction of an exchange morphism to the open part

Consider a square of categories
```
C₃ --iS--> C₄
|          |
pL         qL
v          v
C₁ --jS--> C₂
```
with adjunctions `pU ⊣ pL`, `qU ⊣ qL`, `jS ⊣ jU` and `iS ⊣ iU`, and a comparison
`θ : jU ⋙ pU ⟶ qU ⋙ iU`. In the application `C₁ = D(X)`, `C₂ = D(Z)`, `C₃ = D(X')`,
`C₄ = D(Z')` for a cartesian square of schemes
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` and `i'` open immersions, `jS = j_!`, `iS = i'_!`, `pU ⊣ pL` and `qU ⊣ qL` are
`Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`, and `θ : Lp^* Lj^* ≅ Li'^* Lp'^*` is the pullback comparison
of the square. From `θ` one builds:

* the *base-change morphism for extension by zero* `bco : iS ∘ pU ⟶ qU ∘ jS`, the mate of `θ`
  under `jS ⊣ jU` and `iS ⊣ iU`;
* the *exchange morphism* `jS ∘ pL ⟶ qL ∘ iS`, the mate of an inverse `β` of `bco` under
  `pU ⊣ pL` and `qU ⊣ qL`;
* the *base-change morphism for the pushforward* `jU ∘ qL ⟶ pL ∘ iU`, the mate of `θ` under
  `pU ⊣ pL` and `qU ⊣ qL`.

This file shows that the restriction `jU` of the exchange morphism, precomposed with the unit
of `jS ⊣ jU` and followed by the base-change morphism for the pushforward, is `pL` applied to
the unit of `iS ⊣ iU` (`CategoryTheory.Adjunction.unit_app_comp_map_exchange_comp_baseChange`).
In particular, if the units of `jS ⊣ jU` and `iS ⊣ iU` are isomorphisms (`j_!` and `i'_!` are
fully faithful) and the base-change morphism for the pushforward is an isomorphism, then the
restriction of the exchange morphism along `jU` is an isomorphism
(`CategoryTheory.Adjunction.isIso_map_exchange`).

-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  {pU : C₁ ⥤ C₃} {pL : C₃ ⥤ C₁} {qU : C₂ ⥤ C₄} {qL : C₄ ⥤ C₂}
  {jS : C₁ ⥤ C₂} {jU : C₂ ⥤ C₁} {iS : C₃ ⥤ C₄} {iU : C₄ ⥤ C₃}
  (ap : pU ⊣ pL) (aq : qU ⊣ qL) (aj : jS ⊣ jU) (ai : iS ⊣ iU) (θ : jU ⋙ pU ⟶ qU ⋙ iU)

/-- **The open restriction of the exchange morphism.** Let `β : qU (jS M) ⟶ iS (pU M)` be a
left inverse of the component at `M = pL K` of the mate `iS (pU M) ⟶ qU (jS M)` of `θ` under
`jS ⊣ jU` and `iS ⊣ iU`. Then the composite of the unit of `jS ⊣ jU`, of `jU` applied to the
exchange morphism `jS (pL K) ⟶ qL (iS K)` (the mate of `β`), and of the base-change morphism
`jU (qL N) ⟶ pL (iU N)` at `N = iS K` (the mate of `θ` under `pU ⊣ pL` and `qU ⊣ qL`), is
`pL` applied to the unit `K ⟶ iU (iS K)` of `iS ⊣ iU`. -/
lemma unit_app_comp_map_exchange_comp_baseChange (K : C₃)
    (β : qU.obj (jS.obj (pL.obj K)) ⟶ iS.obj (pU.obj (pL.obj K)))
    (hβ : (iS.map (pU.map (aj.unit.app (pL.obj K))) ≫ iS.map (θ.app (jS.obj (pL.obj K))) ≫
      ai.counit.app (qU.obj (jS.obj (pL.obj K)))) ≫ β = 𝟙 _) :
    aj.unit.app (pL.obj K) ≫
        jU.map (aq.unit.app (jS.obj (pL.obj K)) ≫ qL.map β ≫ qL.map (iS.map (ap.counit.app K))) ≫
        ap.unit.app (jU.obj (qL.obj (iS.obj K))) ≫ pL.map (θ.app (qL.obj (iS.obj K))) ≫
        pL.map (iU.map (aq.counit.app (iS.obj K))) =
      pL.map (ai.unit.app K) := by
  -- `pU η ≫ θ` is the adjoint transpose under `iS ⊣ iU` of the mate of `θ`, of which `β` is a
  -- left inverse.
  have h₁ : pU.map (aj.unit.app (pL.obj K)) ≫ θ.app (jS.obj (pL.obj K)) ≫ iU.map β =
      ai.unit.app (pU.obj (pL.obj K)) := by
    have h := (ai.homEquiv _ _).apply_symm_apply
      (pU.map (aj.unit.app (pL.obj K)) ≫ θ.app (jS.obj (pL.obj K)))
    rw [homEquiv_counit, homEquiv_unit] at h
    rw [iS.map_comp, Category.assoc] at h
    rw [← Category.assoc, ← h, Category.assoc, ← iU.map_comp, hβ, iU.map_id]
    exact Category.comp_id _
  -- The adjoint transpose of `η ≫ qL h` under `qU ⊣ qL` is `h`.
  have h₂ : qU.map (aq.unit.app (jS.obj (pL.obj K)) ≫ qL.map β ≫
      qL.map (iS.map (ap.counit.app K))) ≫ aq.counit.app (iS.obj K) =
        β ≫ iS.map (ap.counit.app K) := by
    have h := (aq.homEquiv _ _).symm_apply_apply (β ≫ iS.map (ap.counit.app K))
    rw [homEquiv_counit, homEquiv_unit, qL.map_comp] at h
    exact h
  have hθ := θ.naturality (aq.unit.app (jS.obj (pL.obj K)) ≫ qL.map β ≫
    qL.map (iS.map (ap.counit.app K)))
  have hη := ap.unit.naturality (aj.unit.app (pL.obj K) ≫ jU.map (aq.unit.app (jS.obj (pL.obj K)) ≫
    qL.map β ≫ qL.map (iS.map (ap.counit.app K))))
  have hι := ai.unit.naturality (ap.counit.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hθ hι hη
  rw [reassoc_of% hη, ← pL.map_comp, ← pL.map_comp,
    pU.map_comp, Category.assoc, reassoc_of% hθ, ← iU.map_comp, h₂, iU.map_comp,
    reassoc_of% h₁, ← hι, pL.map_comp, ap.right_triangle_components_assoc]

/-- **The open restriction of the exchange morphism is an isomorphism** as soon as the units of
`jS ⊣ jU` and `iS ⊣ iU` and the base-change morphism `jU (qL N) ⟶ pL (iU N)` at `N = iS K`
are isomorphisms: this follows from
`CategoryTheory.Adjunction.unit_app_comp_map_exchange_comp_baseChange`. -/
lemma isIso_map_exchange (K : C₃) (β : qU.obj (jS.obj (pL.obj K)) ⟶ iS.obj (pU.obj (pL.obj K)))
    (hβ : (iS.map (pU.map (aj.unit.app (pL.obj K))) ≫ iS.map (θ.app (jS.obj (pL.obj K))) ≫
      ai.counit.app (qU.obj (jS.obj (pL.obj K)))) ≫ β = 𝟙 _)
    [IsIso (aj.unit.app (pL.obj K))] [IsIso (ai.unit.app K)]
    [IsIso (ap.unit.app (jU.obj (qL.obj (iS.obj K))) ≫ pL.map (θ.app (qL.obj (iS.obj K))) ≫
      pL.map (iU.map (aq.counit.app (iS.obj K))))] :
    IsIso (jU.map (aq.unit.app (jS.obj (pL.obj K)) ≫ qL.map β ≫
      qL.map (iS.map (ap.counit.app K)))) := by
  have h := unit_app_comp_map_exchange_comp_baseChange ap aq aj ai θ K β hβ
  have : IsIso (aj.unit.app (pL.obj K) ≫ jU.map (aq.unit.app (jS.obj (pL.obj K)) ≫
      qL.map β ≫ qL.map (iS.map (ap.counit.app K))) ≫ ap.unit.app (jU.obj (qL.obj (iS.obj K))) ≫
      pL.map (θ.app (qL.obj (iS.obj K))) ≫ pL.map (iU.map (aq.counit.app (iS.obj K)))) := by
    rw [h]
    infer_instance
  have := IsIso.of_isIso_comp_left (aj.unit.app (pL.obj K))
    (jU.map (aq.unit.app (jS.obj (pL.obj K)) ≫ qL.map β ≫ qL.map (iS.map (ap.counit.app K))) ≫
      ap.unit.app (jU.obj (qL.obj (iS.obj K))) ≫ pL.map (θ.app (qL.obj (iS.obj K))) ≫
        pL.map (iU.map (aq.counit.app (iS.obj K))))
  exact IsIso.of_isIso_comp_right _
    (ap.unit.app (jU.obj (qL.obj (iS.obj K))) ≫ pL.map (θ.app (qL.obj (iS.obj K))) ≫
      pL.map (iU.map (aq.counit.app (iS.obj K))))

section Exchange

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']

/-- The *exchange morphism* `Rf ⋙ G ⟶ G' ⋙ Rf'` of a natural isomorphism
`θ : G ⋙ Lf' ≅ Lf ⋙ G'` between left adjoints `Lf ⊣ Rf` and `Lf' ⊣ Rf'`, the composite of the
unit insertion, the square transport of `θ`, and the counit contraction (this is the shape of
the base-change morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*`). -/
def exchangeRight {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'} {G : B ⥤ B'}
    {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G') :
    Rf ⋙ G ⟶ G' ⋙ Rf' :=
  ((Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (Rf ⋙ G) af'.unit) ≫
    (Functor.squareTransport Rf Rf' θ).hom ≫
      (Functor.whiskerRight af.counit (G' ⋙ Rf') ≫ (Functor.leftUnitor _).hom)

/-- The component of `exchangeRight af af' θ` at `K`. -/
lemma exchangeRight_app {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'} {G : B ⥤ B'}
    {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G') (K : A) :
    (exchangeRight af af' θ).app K = af'.unit.app (G.obj (Rf.obj K)) ≫
      Rf'.map (θ.hom.app (Rf.obj K)) ≫ Rf'.map (G'.map (af.counit.app K)) := by
  simp [exchangeRight]

/-- The *exchange morphism* `H ⋙ jS' ⟶ jS ⋙ H'` of a natural isomorphism
`θ : jU ⋙ H ≅ H' ⋙ jU'` between right adjoints `jS ⊣ jU` and `jS' ⊣ jU'`, the composite of the
unit insertion, the square transport of `θ`, and the counit contraction (this is the shape of
the base-change morphism `Lg'^* j'_! ⟶ j_! Lg^*` for extension by zero). -/
def exchangeLeft {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'} {jU' : B' ⥤ A'} {H : A ⥤ A'}
    {H' : B ⥤ B'} (aj : jS ⊣ jU) (aj' : jS' ⊣ jU') (θ : jU ⋙ H ≅ H' ⋙ jU') :
    H ⋙ jS' ⟶ jS ⋙ H' :=
  ((Functor.leftUnitor _).inv ≫ Functor.whiskerRight aj.unit (H ⋙ jS')) ≫
    (Functor.squareTransport jS jS' θ).hom ≫
      (Functor.whiskerLeft (jS ⋙ H') aj'.counit ≫ (Functor.rightUnitor _).hom)

/-- The component of `exchangeLeft aj aj' θ` at `K`. -/
lemma exchangeLeft_app {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'} {jU' : B' ⥤ A'} {H : A ⥤ A'}
    {H' : B ⥤ B'} (aj : jS ⊣ jU) (aj' : jS' ⊣ jU') (θ : jU ⋙ H ≅ H' ⋙ jU') (K : A) :
    (exchangeLeft aj aj' θ).app K = jS'.map (H.map (aj.unit.app K)) ≫
      jS'.map (θ.hom.app (jS.obj K)) ≫ aj'.counit.app (H'.obj (jS.obj K)) := by
  simp [exchangeLeft]

/-- **The restriction of the exchange morphism of left adjoints to the open part.** If the units
of `jS ⊣ jU` and `jS' ⊣ jU'` are isomorphisms (the left adjoints are fully faithful, as the
extensions by zero along open immersions), then `jU'` of every component of
`exchangeLeft aj aj' θ` is an isomorphism: it is the composite of `jU' jS'` applied to the unit
of `jS ⊣ jU` and to `θ`, and of `jU'` applied to the counit of `jS' ⊣ jU'`, which is inverse
to the unit of `jS' ⊣ jU'` by the triangle identity. -/
lemma isIso_map_exchangeLeft_app {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'} {jU' : B' ⥤ A'}
    {H : A ⥤ A'} {H' : B ⥤ B'} (aj : jS ⊣ jU) (aj' : jS' ⊣ jU') (θ : jU ⋙ H ≅ H' ⋙ jU')
    [IsIso aj.unit] [IsIso aj'.unit] (K : A) :
    IsIso (jU'.map ((exchangeLeft aj aj' θ).app K)) := by
  rw [exchangeLeft_app, jU'.map_comp, jU'.map_comp]
  have : IsIso (jU'.map (aj'.counit.app (H'.obj (jS.obj K)))) := by
    have : IsIso (aj'.unit.app (jU'.obj (H'.obj (jS.obj K))) ≫
        jU'.map (aj'.counit.app (H'.obj (jS.obj K)))) := by
      rw [aj'.right_triangle_components]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (aj'.unit.app _) _
  infer_instance

end Exchange

/-- **The open restriction of the exchange morphism is an isomorphism.** Let
`e : jS ⋙ qU ≅ pU ⋙ iS` be an isomorphism whose inverse is the exchange morphism
`exchangeLeft aj ai θ` (base change for extension by zero), and consider the exchange morphism
`exchangeRight ap aq e : pL ⋙ jS ⟶ iS ⋙ qL`. If the units of `jS ⊣ jU` and `iS ⊣ iU` are
isomorphisms and the exchange morphism `exchangeRight aq ap θ : qL ⋙ jU ⟶ iU ⋙ pL` (base change
for the pushforward) is an isomorphism at `iS K`, then `jU` of the component at `K` of
`exchangeRight ap aq e` is an isomorphism. -/
theorem isIso_map_exchangeRight_app (θ : jU ⋙ pU ≅ qU ⋙ iU) (e : jS ⋙ qU ≅ pU ⋙ iS)
    (he : e.inv = exchangeLeft aj ai θ) (K : C₃) [IsIso (aj.unit.app (pL.obj K))]
    [IsIso (ai.unit.app K)] [IsIso ((exchangeRight aq ap θ).app (iS.obj K))] :
    IsIso (jU.map ((exchangeRight ap aq e).app K)) := by
  rw [exchangeRight_app] at *
  refine isIso_map_exchange ap aq aj ai θ.hom K (e.hom.app (pL.obj K)) ?_
  have h := e.inv_hom_id_app (pL.obj K)
  rw [he, exchangeLeft_app] at h
  simp only [Category.assoc] at h ⊢
  exact h

end CategoryTheory.Adjunction
