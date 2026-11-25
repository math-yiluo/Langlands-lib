/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!

# Pairings with the evaluation, and their transport along monoidal functors

This file collects the category-theoretic statements behind
`WeilConjectures.TraceFormula.KunnethVerdierOpen`, for abstract monoidal (closed, braided)
categories and functors, so that the diagram chases are carried out once and for all away from
the bounded constructible derived categories.

## Main definitions

- `CategoryTheory.MonoidalClosed.swapEvPairing`: for a lax monoidal functor `Q : C ⥤ E` and
  `α : P ⊗ Q ω ⟶ T`, the pairing
  `Q N ⊗ (P ⊗ Q [N, ω]) ⟶ P ⊗ (Q N ⊗ Q [N, ω]) ⟶ P ⊗ Q (N ⊗ [N, ω]) ⟶ P ⊗ Q ω ⟶ T`.
  The Künneth–Verdier pairing is the case `Q = Lp_Y^*`, `α` the exceptional Künneth map.
- `CategoryTheory.MonoidalClosed.preIsoApp`: `[A, T] ≅ [A', T]` for `A ≅ A'`.

## Main statements

- `CategoryTheory.MonoidalClosed.μ_map_swapEvPairing`: a strong monoidal braided functor `G`
  carries `swapEvPairing Q α` to `swapEvPairing Q' α'`, given a (not necessarily invertible)
  comparison `σ : Q ⋙ G ⟶ J ⋙ Q'` compatible with the tensor structures and a compatibility
  of `α` and `α'`.
- `CategoryTheory.Functor.Monoidal.μ_comp_hom_app_of_δ`: a natural isomorphism `F ≅ P ⋙ R` of
  strong monoidal functors compatible with the comonoidal structures is compatible with the
  monoidal structures.
- `CategoryTheory.MonoidalClosed.map_curry_comp`: the transposes of compatible pairings form a
  commutative square through the internal-hom comparison of `G`.
- `CategoryTheory.Adjunction.isIso_of_isIso_map_of_isIso_counit`: for `F ⊣ H` with invertible
  counit, a morphism between objects in the essential image of `H` is invertible as soon as its
  image under `F` is.

-/

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed Functor.LaxMonoidal

namespace CategoryTheory

namespace MonoidalCategory

variable {E : Type*} [Category* E] [MonoidalCategory E] [BraidedCategory E]

/-- The symmetry `n ⊗ (P ⊗ d) ⟶ P ⊗ (n ⊗ d)` is natural in `n`, `P` and `d`. -/
@[reassoc]
lemma tensorHom_comp_swap {n n' P P' d d' : E} (x : n ⟶ n') (y : P ⟶ P') (z : d ⟶ d') :
    (x ⊗ₘ (y ⊗ₘ z)) ≫ (α_ n' P' d').inv ≫ (β_ n' P').hom ▷ d' ≫ (α_ P' n' d').hom =
      (α_ n P d).inv ≫ (β_ n P).hom ▷ d ≫ (α_ P n d).hom ≫ (y ⊗ₘ (x ⊗ₘ z)) := by
  rw [associator_inv_naturality_assoc, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    BraidedCategory.braiding_naturality, Category.comp_id, ← Category.id_comp z,
    ← tensorHom_comp_tensorHom_assoc, associator_naturality, tensorHom_id, Category.id_comp]

variable {E' : Type*} [Category* E'] [MonoidalCategory E'] [BraidedCategory E']

/-- A strong monoidal functor compatible with the braidings carries the symmetry
`n ⊗ (P ⊗ d) ⟶ P ⊗ (n ⊗ d)` to the symmetry of the images, through its tensor structure. -/
@[reassoc]
lemma μ_map_swap (G : E ⥤ E') [G.Monoidal]
    (hbr : ∀ K M : E, μ G K M ≫ G.map (β_ K M).hom = (β_ (G.obj K) (G.obj M)).hom ≫ μ G M K)
    (n P d : E) :
    μ G n (P ⊗ d) ≫ G.map (α_ n P d).inv ≫ G.map ((β_ n P).hom ▷ d) ≫ G.map (α_ P n d).hom =
      G.obj n ◁ Functor.OplaxMonoidal.δ G P d ≫ (α_ _ _ _).inv ≫ (β_ _ _).hom ▷ _ ≫
        (α_ _ _ _).hom ≫ G.obj P ◁ μ G n d ≫ μ G P (n ⊗ d) := by
  rw [Functor.Monoidal.map_associator_inv, Functor.Monoidal.map_whiskerRight,
    Functor.Monoidal.map_associator]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [← comp_whiskerRight_assoc, hbr, comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc (μ G P n), Functor.Monoidal.μ_δ, id_whiskerRight, Category.id_comp]

end MonoidalCategory

namespace Functor.Monoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E]

/-- A natural isomorphism `c : F ≅ P ⋙ R` of strong monoidal functors compatible with the
comonoidal structures is compatible with the monoidal structures. -/
@[reassoc]
lemma μ_comp_hom_app_of_δ (F : C ⥤ D) (P : C ⥤ E) (R : E ⥤ D) [F.Monoidal] [P.Monoidal]
    [R.Monoidal] (c : F ≅ P ⋙ R)
    (h : ∀ K M : C, OplaxMonoidal.δ F K M ≫ (c.hom.app K ⊗ₘ c.hom.app M) =
      c.hom.app (K ⊗ M) ≫ R.map (OplaxMonoidal.δ P K M) ≫ OplaxMonoidal.δ R _ _) (K M : C) :
    μ F K M ≫ c.hom.app (K ⊗ M) =
      (c.hom.app K ⊗ₘ c.hom.app M) ≫ μ R (P.obj K) (P.obj M) ≫ R.map (μ P K M) := by
  rw [← cancel_epi (OplaxMonoidal.δ F K M), δ_μ_assoc, reassoc_of% h, δ_μ_assoc,
    ← R.map_comp, δ_μ, R.map_id, Category.comp_id]

/-- The inverse of a natural isomorphism `c : F ≅ P ⋙ R` of strong monoidal functors compatible
with the comonoidal structures is compatible with the monoidal structures. -/
@[reassoc]
lemma μ_comp_inv_app_of_δ (F : C ⥤ D) (P : C ⥤ E) (R : E ⥤ D) [F.Monoidal] [P.Monoidal]
    [R.Monoidal] (c : F ≅ P ⋙ R)
    (h : ∀ K M : C, OplaxMonoidal.δ F K M ≫ (c.hom.app K ⊗ₘ c.hom.app M) =
      c.hom.app (K ⊗ M) ≫ R.map (OplaxMonoidal.δ P K M) ≫ OplaxMonoidal.δ R _ _) (K M : C) :
    μ R (P.obj K) (P.obj M) ≫ R.map (μ P K M) ≫ c.inv.app (K ⊗ M) =
      (c.inv.app K ⊗ₘ c.inv.app M) ≫ μ F K M := by
  rw [← cancel_epi (c.hom.app K ⊗ₘ c.hom.app M), ← μ_comp_hom_app_of_δ_assoc F P R c h,
    Iso.hom_inv_id_app, Category.comp_id, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app, tensorHom_id, id_whiskerRight, Category.id_comp]

end Functor.Monoidal

namespace MonoidalClosed

section Pairing

variable {C E : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  [Category* E] [MonoidalCategory E] [BraidedCategory E]

/-- For a lax monoidal functor `Q : C ⥤ E` and `α : P ⊗ Q ω ⟶ T`, the pairing
```
Q N ⊗ (P ⊗ Q [N, ω]) ≅ P ⊗ (Q N ⊗ Q [N, ω]) ⟶ P ⊗ Q (N ⊗ [N, ω]) ⟶ P ⊗ Q ω ⟶ T
```
built from the symmetry, the tensor structure of `Q`, the evaluation and `α`. -/
def swapEvPairing (Q : C ⥤ E) [Q.LaxMonoidal] {P T : E} {ω : C} (α : P ⊗ Q.obj ω ⟶ T)
    (N : C) : Q.obj N ⊗ (P ⊗ Q.obj ((ihom N).obj ω)) ⟶ T :=
  (α_ _ _ _).inv ≫ ((β_ _ _).hom ▷ _) ≫ (α_ _ _ _).hom ≫ (_ ◁ μ Q _ _) ≫
    (_ ◁ Q.map ((ihom.ev N).app ω)) ≫ α

end Pairing

section Restriction

variable {C₁ C₂ E₁ E₂ : Type*} [Category* C₁] [MonoidalCategory C₁] [MonoidalClosed C₁]
  [Category* C₂] [MonoidalCategory C₂] [MonoidalClosed C₂]
  [Category* E₁] [MonoidalCategory E₁] [BraidedCategory E₁]
  [Category* E₂] [MonoidalCategory E₂] [BraidedCategory E₂]

/-- **Restriction of a pairing `swapEvPairing`**. Let `G : E₁ ⥤ E₂` be strong monoidal and
compatible with the braidings, `σ : Q ⋙ G ⟶ J ⋙ Q'` compatible with the tensor structures of the
lax monoidal functors `Q`, `Q'`, `J`, and `α : P ⊗ Q ω ⟶ T`, `α' : P' ⊗ Q' ω' ⟶ T'` compatible
through `φ : G P ⟶ P'`, `w : J ω ⟶ ω'`, `t : G T ⟶ T'`. Then `G (swapEvPairing Q α N)` is
`swapEvPairing Q' α' (J N)`, through `σ_N`, `φ`, `σ` and the internal-hom comparison of `J`. -/
lemma μ_map_swapEvPairing (Q : C₁ ⥤ E₁) [Q.LaxMonoidal] (Q' : C₂ ⥤ E₂) [Q'.LaxMonoidal]
    (J : C₁ ⥤ C₂) [J.LaxMonoidal] (G : E₁ ⥤ E₂) [G.Monoidal]
    (hbr : ∀ K M : E₁, μ G K M ≫ G.map (β_ K M).hom = (β_ (G.obj K) (G.obj M)).hom ≫ μ G M K)
    (σ : Q ⋙ G ⟶ J ⋙ Q')
    (hσ : ∀ A B : C₁, μ G (Q.obj A) (Q.obj B) ≫ G.map (μ Q A B) ≫ σ.app (A ⊗ B) =
      (σ.app A ⊗ₘ σ.app B) ≫ μ Q' (J.obj A) (J.obj B) ≫ Q'.map (μ J A B))
    {P T : E₁} {P' T' : E₂} {ω : C₁} {ω' : C₂} (φ : G.obj P ⟶ P') (w : J.obj ω ⟶ ω')
    (t : G.obj T ⟶ T') (α : P ⊗ Q.obj ω ⟶ T) (α' : P' ⊗ Q'.obj ω' ⟶ T')
    (hα : μ G P (Q.obj ω) ≫ G.map α ≫ t = (φ ⊗ₘ (σ.app ω ≫ Q'.map w)) ≫ α') (N : C₁) :
    μ G (Q.obj N) (P ⊗ Q.obj ((ihom N).obj ω)) ≫ G.map (swapEvPairing Q α N) ≫ t =
      (σ.app N ⊗ₘ (Functor.OplaxMonoidal.δ G P _ ≫ (φ ⊗ₘ (σ.app _ ≫
        Q'.map ((ihomComparison J N).app ω ≫ (ihom (J.obj N)).map w))))) ≫
        swapEvPairing Q' α' (J.obj N) := by
  have hα' : G.map α ≫ t = Functor.OplaxMonoidal.δ G P (Q.obj ω) ≫
      (φ ⊗ₘ (σ.app ω ≫ Q'.map w)) ≫ α' := by
    rw [← hα, Functor.Monoidal.δ_μ_assoc]
  have hK : μ G (Q.obj N) (Q.obj ((ihom N).obj ω)) ≫ G.map (μ Q _ _) ≫
      G.map (Q.map ((ihom.ev N).app ω)) ≫ σ.app ω ≫ Q'.map w =
      (σ.app N ⊗ₘ (σ.app _ ≫ Q'.map ((ihomComparison J N).app ω ≫
        (ihom (J.obj N)).map w))) ≫ μ Q' _ _ ≫ Q'.map ((ihom.ev (J.obj N)).app ω') := by
    have hn : G.map (Q.map ((ihom.ev N).app ω)) ≫ σ.app ω =
        σ.app (N ⊗ (ihom N).obj ω) ≫ Q'.map (J.map ((ihom.ev N).app ω)) :=
      σ.naturality ((ihom.ev N).app ω)
    rw [reassoc_of% hn, reassoc_of% hσ, ← Q'.map_comp, ← Q'.map_comp,
      ← ihomComparison_ev_assoc, ← ihom.ev_naturality]
    simp only [Q'.map_comp, ← MonoidalCategory.whiskerLeft_comp_assoc]
    simp [tensorHom_def]
  have hR : G.obj P ◁ μ G (Q.obj N) (Q.obj ((ihom N).obj ω)) ≫ G.obj P ◁ G.map (μ Q _ _) ≫
      G.obj P ◁ G.map (Q.map ((ihom.ev N).app ω)) ≫ (φ ⊗ₘ (σ.app ω ≫ Q'.map w)) =
      (φ ⊗ₘ (σ.app N ⊗ₘ (σ.app _ ≫ Q'.map ((ihomComparison J N).app ω ≫
        (ihom (J.obj N)).map w)))) ≫ P' ◁ μ Q' _ _ ≫
          P' ◁ Q'.map ((ihom.ev (J.obj N)).app ω') := by
    rw [tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
    simp only [Category.assoc]
    rw [hK, whisker_exchange, tensorHom_def φ]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rfl
  simp only [swapEvPairing, G.map_comp, Category.assoc]
  rw [μ_map_swap_assoc G hbr, hα', ← μ_natural_right_assoc, ← μ_natural_right_assoc]
  dsimp only [Functor.id_obj]
  rw [Functor.Monoidal.μ_δ_assoc, reassoc_of% hR, ← tensorHom_comp_swap_assoc,
    whiskerLeft_comp_tensorHom_assoc]

end Restriction

section Curry

variable {C D : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]
  [Category* D] [MonoidalCategory D] [MonoidalClosed D]

/-- Precomposition with an isomorphism `a : A ≅ A'`, as an isomorphism `[A, T] ≅ [A', T]`. -/
@[simps]
def preIsoApp {A A' : D} (a : A ≅ A') (T : D) : (ihom A).obj T ≅ (ihom A').obj T where
  hom := (pre a.inv).app T
  inv := (pre a.hom).app T
  hom_inv_id := by rw [← NatTrans.comp_app, ← pre_map, a.hom_inv_id, pre_id, NatTrans.id_app]
  inv_hom_id := by rw [← NatTrans.comp_app, ← pre_map, a.inv_hom_id, pre_id, NatTrans.id_app]

/-- **Transposes of compatible pairings along a lax monoidal functor.** If the pairings
`p : A ⊗ B ⟶ T` and `p' : A' ⊗ B' ⟶ T'` are compatible along `G` through `a : G A ≅ A'`,
`b : G B ⟶ B'` and `t : G T ⟶ T'`, then `G (curry p)` followed by the internal-hom comparison
`G [A, T] ⟶ [G A, G T] ⟶ [G A, T'] ⟶ [A', T']` is `b ≫ curry p'`. -/
lemma map_curry_comp (G : C ⥤ D) [G.LaxMonoidal] {A B T : C} {A' B' T' : D}
    (p : A ⊗ B ⟶ T) (p' : A' ⊗ B' ⟶ T') (a : G.obj A ≅ A') (b : G.obj B ⟶ B')
    (t : G.obj T ⟶ T') (h : μ G A B ≫ G.map p ≫ t = (a.hom ⊗ₘ b) ≫ p') :
    G.map (curry p) ≫ (ihomComparison G A).app T ≫ (ihom (G.obj A)).map t ≫
      (pre a.inv).app T' = b ≫ curry p' := by
  have hu : uncurry (G.map (curry p) ≫ (ihomComparison G A).app T) =
      μ G A B ≫ G.map p := by
    rw [uncurry_natural_left, uncurry_eq, ihomComparison_ev, μ_natural_right_assoc,
      ← G.map_comp, ← uncurry_eq, uncurry_curry]
  apply uncurry_injective
  rw [← Category.assoc, ← Category.assoc, uncurry_pre_app, uncurry_natural_right, hu,
    uncurry_natural_left, uncurry_curry, Category.assoc, h, whiskerRight_comp_tensorHom_assoc,
    a.inv_hom_id, id_tensorHom]

end Curry

end MonoidalClosed

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]

/-- Let `F ⊣ H` be an adjunction with invertible counit (that is, `H` fully faithful). A morphism
`φ : A ⟶ B` between objects isomorphic to objects in the image of `H` is an isomorphism as soon
as `F φ` is: the unit is invertible at `A` and `B`, and `φ` is conjugate to `H (F φ)`. -/
lemma isIso_of_isIso_map_of_isIso_counit {F : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H)
    [IsIso adj.counit] {A B : C} {A' B' : D} (eA : A ≅ H.obj A') (eB : B ≅ H.obj B')
    (φ : A ⟶ B) [IsIso (F.map φ)] : IsIso φ := by
  have hη (Z : D) : IsIso (adj.unit.app (H.obj Z)) := by
    have : IsIso (adj.unit.app (H.obj Z) ≫ H.map (adj.counit.app Z)) := by
      rw [adj.right_triangle_components]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (H.map (adj.counit.app Z))
  have := hη A'
  have := hη B'
  have : IsIso (adj.unit.app A) := (NatTrans.isIso_app_iff_of_iso adj.unit eA).2 inferInstance
  have : IsIso (adj.unit.app B) := (NatTrans.isIso_app_iff_of_iso adj.unit eB).2 inferInstance
  have h : φ ≫ adj.unit.app B = adj.unit.app A ≫ H.map (F.map φ) := adj.unit.naturality φ
  have : IsIso (φ ≫ adj.unit.app B) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right φ (adj.unit.app B)

end Adjunction

end CategoryTheory
