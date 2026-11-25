/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-!
# Detecting invertibility of a base change map after restriction

Let `adj : F ⊣ G` and `adj' : F' ⊣ G'` be adjunctions, with `F : D ⥤ C` and `F' : D' ⥤ C'`, let
`adj_D : N_D ⊣ R_D` and `adj_C : N_C ⊣ R_C` be adjunctions with `N_D : D ⥤ D'` and
`N_C : C ⥤ C'`, and let `α : N_D ⋙ F' ≅ F ⋙ N_C`. Its mate `β : N_D (G M) ⟶ G' (N_C M)` is the
*base change map*. Write `γ : F (R_D P) ⟶ R_C (F' P)` for the mate of `α⁻¹`.

Suppose that the monads `N_D ⋙ R_D` and `N_C ⋙ R_C` are identified with endofunctors `T_D` and
`T_C` (for instance tensor products with a fixed object), and that `a : F (T_D X) ⟶ T_C (F X)`
corresponds to `γ` followed by `R_C α` under these identifications. Then `R_D β` is, up to
isomorphisms, the mate `G (T_D M) ⟶ T_C (G M)` of `a`. Hence `β` is an isomorphism at `M` as
soon as `R_D` reflects isomorphisms and the mate of `a` is an isomorphism at `M`.

This applies to derived extension of scalars `N = - ⊗ᴸ_R S` along the derived pullback `F = Lg^*`
and the derived direct image `G = Rg_*`: restricted back to `R`, extension of scalars is the
tensor product with `S`, and the mate of `a` is the projection map of `Rg_*` at `S`.

## Main results

- `CategoryTheory.Adjunction.map_mateEquiv_app_comp_mateEquiv_app`: the comparison of `R_D β`
  with the mate of `a`.
- `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_mateEquiv_app`: the criterion for `β`
  to be an isomorphism.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
  {N_D : D ⥤ D'} {N_C : C ⥤ C'} {R_D : D' ⥤ D} {R_C : C' ⥤ C}
  (adj_D : N_D ⊣ R_D) (adj_C : N_C ⊣ R_C) (α : N_D ⋙ F' ≅ F ⋙ N_C)
  {T_D : D ⥤ D} {T_C : C ⥤ C} (ϑ_D : T_D ⟶ N_D ⋙ R_D) (ϑ_C : T_C ⟶ N_C ⋙ R_C)
  (a : T_D ⋙ F ⟶ F ⋙ T_C)

/-- `R_D` of the base change map `β : N_D (G M) ⟶ G' (N_C M)`, the mate of `α`, compared with the
mate `G (T_D M) ⟶ T_C (G M)` of a natural transformation `a : F (T_D X) ⟶ T_C (F X)` which
corresponds to `γ` followed by `R_C α` through `ϑ_D : T_D ⟶ N_D ⋙ R_D` and
`ϑ_C : T_C ⟶ N_C ⋙ R_C`, `γ` being the mate of `α⁻¹`. The last arrow is the iterated mate of
`α⁻¹`, an isomorphism. -/
lemma map_mateEquiv_app_comp_mateEquiv_app
    (h : ∀ X, F.map (ϑ_D.app X) ≫ (mateEquiv adj_D adj_C α.inv).app (N_D.obj X) ≫
      R_C.map (α.hom.app X) = a.app X ≫ ϑ_C.app (F.obj X)) (M : C) :
    ϑ_D.app (G.obj M) ≫ R_D.map ((mateEquiv adj adj' α.hom).app M) ≫
        (mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)).app (N_C.obj M) =
      (mateEquiv adj adj a).app M ≫ G.map (ϑ_C.app M) := by
  apply (adj.homEquiv _ _).symm.injective
  have hκ := mateEquiv_counit adj' adj (mateEquiv adj_D adj_C α.inv) (N_C.obj M)
  have hβ := mateEquiv_counit adj adj' α.hom M
  have hγ := (mateEquiv adj_D adj_C α.inv).naturality ((mateEquiv adj adj' α.hom).app M)
  have ha := mateEquiv_counit adj adj a M
  have hϑ := ϑ_C.naturality (adj.counit.app M)
  dsimp at hκ hβ hγ ha hϑ
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hκ, reassoc_of% hγ, ← R_C.map_comp, hβ, R_C.map_comp, reassoc_of% (h (G.obj M)),
    adj.counit_naturality, reassoc_of% ha, hϑ]

omit adj adj' in
/-- The hypothesis of `CategoryTheory.Adjunction.map_mateEquiv_app_comp_mateEquiv_app` in
transposed form: it holds at `X` as soon as the transposes along `N_C ⊣ R_C` of both sides agree,
which avoids the unit of `N_C ⊣ R_C`: `F' (ϑ_D♯ X) ≫ α X = α (T_D X) ≫ N_C (a X ≫ ϑ_C (F X)) ≫ ε`,
where `ϑ_D♯ X = N_D (ϑ_D X) ≫ ε` is the transpose of `ϑ_D X` along `N_D ⊣ R_D`. -/
lemma map_comp_mateEquiv_app_comp_map_of_transpose (X : D)
    (h : F'.map (N_D.map (ϑ_D.app X) ≫ adj_D.counit.app (N_D.obj X)) ≫ α.hom.app X =
      α.hom.app (T_D.obj X) ≫ N_C.map (a.app X ≫ ϑ_C.app (F.obj X)) ≫
        adj_C.counit.app (N_C.obj (F.obj X))) :
    F.map (ϑ_D.app X) ≫ (mateEquiv adj_D adj_C α.inv).app (N_D.obj X) ≫
      R_C.map (α.hom.app X) = a.app X ≫ ϑ_C.app (F.obj X) := by
  apply (adj_C.homEquiv _ _).symm.injective
  have hγ := mateEquiv_counit adj_D adj_C α.inv (N_D.obj X)
  have hα := α.inv.naturality (ϑ_D.app X)
  dsimp at hγ hα
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, counit_naturality]
  rw [reassoc_of% hγ, reassoc_of% hα, ← Functor.map_comp_assoc, h, Iso.inv_hom_id_app_assoc,
    Functor.map_comp, Category.assoc]
  rfl

include adj' adj_C in
/-- **Invertibility of the base change map after restriction.** With the notation of
`CategoryTheory.Adjunction.map_mateEquiv_app_comp_mateEquiv_app`, if `ϑ_D` and `ϑ_C` are
isomorphisms, `R_D` reflects isomorphisms and the mate `G (T_D M) ⟶ T_C (G M)` of `a` is an
isomorphism at `M`, then so is the base change map `N_D (G M) ⟶ G' (N_C M)`. -/
theorem isIso_mateEquiv_app_of_isIso_mateEquiv_app [IsIso ϑ_D] [IsIso ϑ_C]
    [R_D.ReflectsIsomorphisms]
    (h : ∀ X, F.map (ϑ_D.app X) ≫ (mateEquiv adj_D adj_C α.inv).app (N_D.obj X) ≫
      R_C.map (α.hom.app X) = a.app X ≫ ϑ_C.app (F.obj X)) (M : C)
    [IsIso ((mateEquiv adj adj a).app M)] :
    IsIso ((mateEquiv adj adj' α.hom).app M) := by
  have : IsIso (mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)) :=
    isIso_mateEquiv_mateEquiv adj_D adj_C α.symm adj adj'
  have e := map_mateEquiv_app_comp_mateEquiv_app adj adj' adj_D adj_C α ϑ_D ϑ_C a h M
  have : IsIso (ϑ_D.app (G.obj M) ≫ R_D.map ((mateEquiv adj adj' α.hom).app M) ≫
      (mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)).app (N_C.obj M)) := by
    rw [e]
    infer_instance
  have : IsIso (R_D.map ((mateEquiv adj adj' α.hom).app M) ≫
      (mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)).app (N_C.obj M)) :=
    IsIso.of_isIso_comp_left (ϑ_D.app (G.obj M)) _
  have : IsIso (R_D.map ((mateEquiv adj adj' α.hom).app M)) :=
    IsIso.of_isIso_comp_right _
      ((mateEquiv adj' adj (mateEquiv adj_D adj_C α.inv)).app (N_C.obj M))
  exact isIso_of_reflects_iso _ R_D

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

section ProjectionMap

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)
  {L : D} {L' : C} (c : F.obj L ⟶ L') {T_D' : D ⥤ D} {T_C' : C ⥤ C}
  (e_D : T_D' ≅ T_D.flip.obj L) (e_C : T_C' ≅ T_C.flip.obj L') (a : T_D' ⋙ F ⟶ F ⋙ T_C')

/-- Let `a : F (T_D' X) ⟶ T_C' (F X)` be identified, through isomorphisms `T_D' ≅ T_D (-, L)` and
`T_C' ≅ T_C (-, L')`, with the comparison `φ : F (T_D X L) ⟶ T_C (F X) (F L)` followed by a
morphism `c : F L ⟶ L'`. Then the mate `T_D' (G M) ⟶ G (T_C' M)` of `a` is identified
with the right adjoint projection map `T_D (G M) L ⟶ G (T_C M (F L))` followed by `G (T_C M c)`. -/
lemma mateEquiv_app_comp_map_eq_rightAdjointProjectionMap
    (h : ∀ X, a.app X ≫ e_C.hom.app (F.obj X) =
      F.map (e_D.hom.app X) ≫ (φ.app X).app L ≫ (T_C.obj (F.obj X)).map c) (M : C) :
    (mateEquiv adj adj a).app M ≫ G.map (e_C.hom.app M) =
      e_D.hom.app (G.obj M) ≫ ((adj.rightAdjointProjectionMap φ).app M).app L ≫
        G.map ((T_C.obj M).map c) := by
  apply (adj.homEquiv _ _).symm.injective
  have hm := mateEquiv_counit adj adj a M
  have hT := (T_C.map (adj.counit.app M)).naturality c
  have he := e_C.hom.naturality (adj.counit.app M)
  dsimp at hm hT he
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, counit_naturality]
  rw [reassoc_of% hm, he, reassoc_of% (h (G.obj M)), hT,
    map_rightAdjointProjectionMap_app_app_comp_counit_assoc]

/-- With the notation of
`CategoryTheory.Adjunction.mateEquiv_app_comp_map_eq_rightAdjointProjectionMap`, the mate of `a`
is an isomorphism at `M` as soon as the projection map at `(M, L)` and `T_C M c` are. -/
lemma isIso_mateEquiv_app_of_isIso_rightAdjointProjectionMap
    (h : ∀ X, a.app X ≫ e_C.hom.app (F.obj X) =
      F.map (e_D.hom.app X) ≫ (φ.app X).app L ≫ (T_C.obj (F.obj X)).map c) (M : C)
    [IsIso (((adj.rightAdjointProjectionMap φ).app M).app L)] [IsIso ((T_C.obj M).map c)] :
    IsIso ((mateEquiv adj adj a).app M) := by
  have e := mateEquiv_app_comp_map_eq_rightAdjointProjectionMap adj φ c e_D e_C a h M
  rw [← IsIso.eq_comp_inv] at e
  rw [e]
  infer_instance

end ProjectionMap

end CategoryTheory.Adjunction
