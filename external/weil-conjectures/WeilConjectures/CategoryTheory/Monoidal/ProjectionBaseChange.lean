/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!

# Projection morphisms, base change and the Verdier exchange along a cartesian square

This file contains the diagram chases, for abstract functors, behind the compatibility of the
Künneth–Verdier map with a closed pushforward in the second factor
(`WeilConjectures.TraceFormula.KunnethVerdierClosed`).

The data model a cartesian square
```
W ──q_W──▶ Z
│G         │g
▼          ▼
V ──q_V──▶ Y
```
with `G` and `g` proper: `G : 𝒱 ⥤ 𝒲` and `g : 𝒵 ⥤ 𝒴` play the compactly supported direct
images, with left adjoints `Gs`, `gs` (the inverse images) and projection morphisms
`PF : G A ⊗ B ⟶ G (A ⊗ Gs B)`, `q : 𝒴 ⥤ 𝒲` and `qZ : 𝒵 ⥤ 𝒱` play the (monoidal) inverse images
along `q_V` and `q_W`, and `BC : g ⋙ q ⟶ qZ ⋙ G` is compact-support base change.

## Main definitions

- `CategoryTheory.ProjectionBaseChange.trace`: the morphism `G (P_Z ⊗ qZ K) ⟶ P ⊗ q L` induced by
  `h : g K ⟶ L`, built from the symmetry, the inverse projection morphism of `G` and the inverse
  base change.
- `CategoryTheory.ProjectionBaseChange.PFBaseChange`: the compatibility of the projection
  morphisms with base change.

## Main statements

- `CategoryTheory.ProjectionBaseChange.whiskerLeft_trace_pairing`: tensoring the trace with
  `q (g N')` and pairing is the trace of the pairing.
- `CategoryTheory.ProjectionBaseChange.trace_comp_curry`: the Künneth–Verdier pairings of `Y` and
  `Z` correspond under the trace and the Verdier exchange of `G`.
- `CategoryTheory.ProjectionBaseChange.isIso_curry_iff`: hence one is an isomorphism if and only if
  the image of the other under `G` is.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.ProjectionBaseChange

section Projection

variable {𝒱 𝒲 : Type*} [Category 𝒱] [Category 𝒲] [MonoidalCategory 𝒱] [MonoidalCategory 𝒲]
  [BraidedCategory 𝒱]

/-- The projection morphism `PF : G A ⊗ B ⟶ G (A ⊗ Gs B)` of `Gs ⊣ G` (characterised by its
compatibility `hcG` with the counit), on `G A ⊗ G (P_Z ⊗ B)` with `P_Z ⟶ Gs P`, can be computed
through `G (P_Z ⊗ B) ⟶ G B ⊗ P`, for a symmetric braiding. -/
lemma projection_braid {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} [Gs.OplaxMonoidal] (aG : Gs ⊣ G)
    (PFG : ∀ (A : 𝒱) (B : 𝒲), G.obj A ⊗ B ⟶ G.obj (A ⊗ Gs.obj B)) [∀ A B, IsIso (PFG A B)]
    (hcG : ∀ A B, Gs.map (PFG A B) ≫ aG.counit.app (A ⊗ Gs.obj B) =
      δ Gs (G.obj A) B ≫ (aG.counit.app A ▷ Gs.obj B))
    (hsymm : ∀ X Y : 𝒱, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    {P : 𝒲} {PZ : 𝒱} (e : PZ ⟶ Gs.obj P) (A B : 𝒱) :
    PFG A (G.obj (PZ ⊗ B)) ≫ G.map (A ◁ aG.counit.app (PZ ⊗ B)) ≫
        G.map ((α_ A PZ B).inv ≫ ((β_ A PZ).hom ▷ B) ≫ (α_ PZ A B).hom ≫
          (β_ PZ (A ⊗ B)).hom ≫ ((A ⊗ B) ◁ e)) ≫ inv (PFG (A ⊗ B) P) =
      (G.obj A ◁ (G.map (β_ PZ B).hom ≫ G.map (B ◁ e) ≫ inv (PFG B P))) ≫ (α_ _ _ _).inv ≫
        (PFG A (G.obj B) ▷ P) ≫ (G.map (A ◁ aG.counit.app B) ▷ P) := by
  rw [← cancel_mono (PFG (A ⊗ B) P)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply (aG.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, hcG]
  have hcG' : Gs.map (inv (PFG B P)) ≫ δ Gs (G.obj B) P ≫ (aG.counit.app B ▷ Gs.obj P) =
      aG.counit.app (B ⊗ Gs.obj P) := by
    rw [← hcG, ← Gs.map_comp_assoc, IsIso.inv_hom_id, Gs.map_id, Category.id_comp]
  simp only [Adjunction.counit_naturality, Adjunction.counit_naturality_assoc]
  rw [reassoc_of% hcG]
  dsimp only [Functor.id_obj]
  simp only [← δ_natural_left_assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  simp only [← δ_natural_left_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight]
  simp only [Category.assoc, Adjunction.counit_naturality]
  rw [reassoc_of% hcG]
  simp only [comp_whiskerRight]
  rw [← associativity_inv_assoc Gs, ← δ_natural_right_assoc Gs]
  congr 1
  rw [← associator_inv_naturality_left_assoc]
  simp only [whisker_exchange_assoc]
  congr 1
  rw [← associator_inv_naturality_middle, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc, Functor.map_comp, hcG', Adjunction.counit_naturality]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, Adjunction.counit_naturality,
    MonoidalCategory.whiskerLeft_comp_assoc]
  congr 1
  have hex : (α_ PZ A B).hom ≫ (β_ PZ (A ⊗ B)).hom = ((β_ PZ A).hom ▷ B) ≫ (α_ A PZ B).hom ≫
      (A ◁ (β_ PZ B).hom) ≫ (α_ A B PZ).inv := by
    rw [← reassoc_of% BraidedCategory.hexagon_forward, Iso.hom_inv_id, Category.comp_id]
  rw [associator_inv_naturality_right, reassoc_of% hex, ← comp_whiskerRight_assoc, hsymm,
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc]

end Projection

section Braiding

variable {𝒲 : Type*} [Category 𝒲] [MonoidalCategory 𝒲] [BraidedCategory 𝒲]

/-- A rearrangement of a pairing `y : Q ⊗ C ⟶ Ω` against `P`, in a symmetric monoidal category. -/
lemma braiding_pairing (hsymm' : ∀ X Y : 𝒲, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    {Q D C P Ω : 𝒲} (x : D ⟶ C) (y : Q ⊗ C ⟶ Ω) :
    (Q ◁ (x ▷ P)) ≫ (Q ◁ (β_ P C).inv) ≫ (α_ Q P C).inv ≫ ((β_ Q P).hom ▷ C) ≫
        (α_ P Q C).hom ≫ (P ◁ y) =
      (α_ Q D P).inv ≫ ((Q ◁ x ≫ y) ▷ P) ≫ (β_ P Ω).inv := by
  have hs : (β_ Q P).hom = (β_ P Q).inv := by
    rw [← cancel_epi (β_ P Q).hom, hsymm', Iso.hom_inv_id]
  have hcore : (Q ◁ (β_ P D).inv) ≫ (α_ Q P D).inv ≫ ((β_ Q P).hom ▷ D) ≫ (α_ P Q D).hom =
      (α_ Q D P).inv ≫ (β_ P (Q ⊗ D)).inv := by
    rw [hs, ← reassoc_of% BraidedCategory.hexagon_forward_inv, Iso.inv_hom_id, Category.comp_id]
  conv_rhs => rw [BraidedCategory.braiding_inv_naturality_left]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, BraidedCategory.braiding_inv_naturality_left,
    MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp,
    reassoc_of% hcore]

end Braiding

section BaseChange

variable {𝒱 𝒲 𝒴 𝒵 : Type*} [Category 𝒱] [Category 𝒲] [Category 𝒴] [Category 𝒵]
  [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [MonoidalCategory 𝒴] [MonoidalCategory 𝒵]

/-- The base change of the projection morphism of `g` against a pairing: for
`hu : (g N' ◁ h) ≫ u = PF_g ≫ g (N' ◁ ε) ≫ h'`, the projection morphism of `G` at
`(qZ N', G (qZ K))`, the counit and the base changes give `q` of `u`. -/
lemma baseChange_pairing {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} (aG : Gs ⊣ G)
    (PFG : ∀ (A : 𝒱) (B : 𝒲), G.obj A ⊗ B ⟶ G.obj (A ⊗ Gs.obj B))
    {g : 𝒵 ⥤ 𝒴} {gs : 𝒴 ⥤ 𝒵} (ag : gs ⊣ g) (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal]
    (BC : g ⋙ q ⟶ qZ ⋙ G) [IsIso BC] (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (hmate : ∀ K, Gs.map (BC.app K) ≫ aG.counit.app (qZ.obj K) =
      θ.hom.app (g.obj K) ≫ qZ.map (ag.counit.app K))
    (PFg : ∀ (A : 𝒵) (B : 𝒴), g.obj A ⊗ B ⟶ g.obj (A ⊗ gs.obj B))
    (hPF2 : ∀ A B, q.map (PFg A B) ≫ BC.app (A ⊗ gs.obj B) ≫ G.map (δ qZ A (gs.obj B)) ≫
      G.map (qZ.obj A ◁ θ.inv.app B) =
        δ q (g.obj A) B ≫ (BC.app A ▷ q.obj B) ≫ PFG (qZ.obj A) (q.obj B))
    (hPFGr : ∀ A {B B' : 𝒲} (f : B ⟶ B'),
      G.obj A ◁ f ≫ PFG A B' = PFG A B ≫ G.map (A ◁ Gs.map f))
    (N' K : 𝒵) {L Ω : 𝒴} (h : g.obj K ⟶ L) (u : g.obj N' ⊗ L ⟶ Ω)
    (h' : g.obj (N' ⊗ K) ⟶ Ω)
    (hu : g.obj N' ◁ h ≫ u = PFg N' (g.obj K) ≫ g.map (N' ◁ ag.counit.app K) ≫ h') :
    (BC.app N' ▷ G.obj (qZ.obj K)) ≫ PFG (qZ.obj N') (G.obj (qZ.obj K)) ≫
        G.map (qZ.obj N' ◁ aG.counit.app (qZ.obj K)) ≫ G.map (Functor.LaxMonoidal.μ qZ N' K) ≫
        inv (BC.app (N' ⊗ K)) ≫ q.map h' =
      (q.obj (g.obj N') ◁ (inv (BC.app K) ≫ q.map h)) ≫ Functor.LaxMonoidal.μ q (g.obj N') L ≫
        q.map u := by
  have h2 : q.map (PFg N' (g.obj K)) ≫ BC.app (N' ⊗ gs.obj (g.obj K)) =
      δ q (g.obj N') (g.obj K) ≫ (BC.app N' ▷ q.obj (g.obj K)) ≫
        PFG (qZ.obj N') (q.obj (g.obj K)) ≫ G.map (qZ.obj N' ◁ θ.hom.app (g.obj K)) ≫
        G.map (Functor.LaxMonoidal.μ qZ N' (gs.obj (g.obj K))) := by
    rw [← reassoc_of% (hPF2 N' (g.obj K))]
    simp only [← G.map_comp, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id_app]
    simp
  have hnat := BC.naturality (N' ◁ ag.counit.app K)
  dsimp at hnat
  have hu' := congrArg q.map hu
  simp only [Functor.map_comp] at hu'
  have key : (BC.app N' ▷ G.obj (qZ.obj K)) ≫ PFG (qZ.obj N') (G.obj (qZ.obj K)) ≫
      G.map (qZ.obj N' ◁ aG.counit.app (qZ.obj K)) ≫ G.map (Functor.LaxMonoidal.μ qZ N' K) =
      (q.obj (g.obj N') ◁ inv (BC.app K)) ≫ Functor.LaxMonoidal.μ q (g.obj N') (g.obj K) ≫
        q.map (PFg N' (g.obj K)) ≫ q.map (g.map (N' ◁ ag.counit.app K)) ≫ BC.app (N' ⊗ K) := by
    rw [hnat, reassoc_of% h2, Functor.Monoidal.μ_δ_assoc,
      ← G.map_comp (Functor.LaxMonoidal.μ qZ N' (gs.obj (g.obj K))),
      ← Functor.LaxMonoidal.μ_natural_right, G.map_comp, ← G.map_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp, ← hmate, MonoidalCategory.whiskerLeft_comp,
      G.map_comp_assoc, ← reassoc_of% (hPFGr (qZ.obj N') (BC.app K)), ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, IsIso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  rw [reassoc_of% key, IsIso.hom_inv_id_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc, hu']

variable [BraidedCategory 𝒱] [BraidedCategory 𝒲]

/-- The *trace* `G (P_Z ⊗ qZ K) ⟶ P ⊗ q L` of `h : g K ⟶ L`: the symmetry, `e : P_Z ⟶ Gs P`, the
inverse projection morphism of `G`, the inverse base change followed by `q h`, and the
symmetry. -/
noncomputable def trace {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} {g : 𝒵 ⥤ 𝒴}
    (PFG : ∀ (A : 𝒱) (B : 𝒲), G.obj A ⊗ B ⟶ G.obj (A ⊗ Gs.obj B)) [∀ A B, IsIso (PFG A B)]
    (q : 𝒴 ⥤ 𝒲) (qZ : 𝒵 ⥤ 𝒱) (BC : g ⋙ q ⟶ qZ ⋙ G) [IsIso BC] (P : 𝒲) {PZ : 𝒱}
    (e : PZ ⟶ Gs.obj P) (K : 𝒵) (L : 𝒴) (h : g.obj K ⟶ L) :
    G.obj (PZ ⊗ qZ.obj K) ⟶ P ⊗ q.obj L :=
  G.map (β_ PZ (qZ.obj K)).hom ≫ G.map (qZ.obj K ◁ e) ≫ inv (PFG (qZ.obj K) P) ≫
    (inv (BC.app K) ≫ q.map h) ▷ P ≫ (β_ P (q.obj L)).inv

/-- **Tensoring the trace with `q (g N')` and pairing is the trace of the pairing**: for a pairing
`u : g N' ⊗ L ⟶ Ω` transposed through the projection morphism of `g` to `h' : g (N' ⊗ K) ⟶ Ω`,
the pairing of `q (g N')` with the trace of `h` is the base change of `q (g N')` to `G (qZ N')`,
the projection morphism of `G`, the counit, the rearrangement and the trace of `h'`. -/
lemma whiskerLeft_trace_pairing {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} [Gs.OplaxMonoidal] (aG : Gs ⊣ G)
    (PFG : ∀ (A : 𝒱) (B : 𝒲), G.obj A ⊗ B ⟶ G.obj (A ⊗ Gs.obj B)) [∀ A B, IsIso (PFG A B)]
    (hcG : ∀ A B, Gs.map (PFG A B) ≫ aG.counit.app (A ⊗ Gs.obj B) =
      δ Gs (G.obj A) B ≫ (aG.counit.app A ▷ Gs.obj B))
    {g : 𝒵 ⥤ 𝒴} {gs : 𝒴 ⥤ 𝒵} (ag : gs ⊣ g) (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal]
    (BC : g ⋙ q ⟶ qZ ⋙ G) [IsIso BC] (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (hmate : ∀ K, Gs.map (BC.app K) ≫ aG.counit.app (qZ.obj K) =
      θ.hom.app (g.obj K) ≫ qZ.map (ag.counit.app K))
    (PFg : ∀ (A : 𝒵) (B : 𝒴), g.obj A ⊗ B ⟶ g.obj (A ⊗ gs.obj B))
    (hPF2 : ∀ A B, q.map (PFg A B) ≫ BC.app (A ⊗ gs.obj B) ≫ G.map (δ qZ A (gs.obj B)) ≫
      G.map (qZ.obj A ◁ θ.inv.app B) =
        δ q (g.obj A) B ≫ (BC.app A ▷ q.obj B) ≫ PFG (qZ.obj A) (q.obj B))
    (hPFGr : ∀ A {B B' : 𝒲} (f : B ⟶ B'),
      G.obj A ◁ f ≫ PFG A B' = PFG A B ≫ G.map (A ◁ Gs.map f))
    (P : 𝒲) {PZ : 𝒱} (e : PZ ⟶ Gs.obj P)
    (hsymm : ∀ X Y : 𝒱, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (hsymm' : ∀ X Y : 𝒲, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (hPFGl : ∀ {A A' : 𝒱} (f : A ⟶ A') (B : 𝒲),
      (G.map f ▷ B) ≫ PFG A' B = PFG A B ≫ G.map (f ▷ Gs.obj B))
    (N' K : 𝒵) {L Ω : 𝒴} (h : g.obj K ⟶ L) (u : g.obj N' ⊗ L ⟶ Ω)
    (h' : g.obj (N' ⊗ K) ⟶ Ω)
    (hu : g.obj N' ◁ h ≫ u = PFg N' (g.obj K) ≫ g.map (N' ◁ ag.counit.app K) ≫ h') :
    (q.obj (g.obj N') ◁ trace PFG q qZ BC P e K L h) ≫ (α_ _ _ _).inv ≫
        ((β_ (q.obj (g.obj N')) P).hom ▷ q.obj L) ≫ (α_ _ _ _).hom ≫
        (P ◁ Functor.LaxMonoidal.μ q (g.obj N') L) ≫ (P ◁ q.map u) =
      (BC.app N' ▷ G.obj (PZ ⊗ qZ.obj K)) ≫ PFG (qZ.obj N') (G.obj (PZ ⊗ qZ.obj K)) ≫
        G.map (qZ.obj N' ◁ aG.counit.app (PZ ⊗ qZ.obj K)) ≫
        G.map ((α_ _ _ _).inv ≫ ((β_ (qZ.obj N') PZ).hom ▷ qZ.obj K) ≫ (α_ _ _ _).hom ≫
          (PZ ◁ Functor.LaxMonoidal.μ qZ N' K)) ≫
        trace PFG q qZ BC P e (N' ⊗ K) Ω h' := by
  have hP := projection_braid aG PFG hcG hsymm e (qZ.obj N') (qZ.obj K)
  have hk := baseChange_pairing aG PFG ag q qZ BC θ hmate PFg hPF2 hPFGr N' K h u h' hu
  have hinvl {A A' : 𝒱} (f : A ⟶ A') (B : 𝒲) :
      G.map (f ▷ Gs.obj B) ≫ inv (PFG A' B) = inv (PFG A B) ≫ (G.map f ▷ B) := by
    rw [IsIso.eq_inv_comp, ← reassoc_of% (hPFGl f B), IsIso.hom_inv_id, Category.comp_id]
  have hbr : G.map ((α_ (qZ.obj N') PZ (qZ.obj K)).inv ≫ ((β_ (qZ.obj N') PZ).hom ▷ qZ.obj K) ≫
      (α_ PZ (qZ.obj N') (qZ.obj K)).hom ≫ (PZ ◁ Functor.LaxMonoidal.μ qZ N' K)) ≫
      G.map (β_ PZ (qZ.obj (N' ⊗ K))).hom ≫ G.map (qZ.obj (N' ⊗ K) ◁ e) ≫
      inv (PFG (qZ.obj (N' ⊗ K)) P) =
      G.map ((α_ (qZ.obj N') PZ (qZ.obj K)).inv ≫ ((β_ (qZ.obj N') PZ).hom ▷ qZ.obj K) ≫
        (α_ PZ (qZ.obj N') (qZ.obj K)).hom ≫ (β_ PZ (qZ.obj N' ⊗ qZ.obj K)).hom ≫
        ((qZ.obj N' ⊗ qZ.obj K) ◁ e)) ≫ inv (PFG (qZ.obj N' ⊗ qZ.obj K) P) ≫
        (G.map (Functor.LaxMonoidal.μ qZ N' K) ▷ P) := by
    rw [← hinvl]
    simp only [← Functor.map_comp_assoc, Category.assoc]
    congr 2
    simp only [BraidedCategory.braiding_naturality_right_assoc, whisker_exchange]
  unfold trace
  rw [reassoc_of% hbr, reassoc_of% hP]
  dsimp only [Functor.comp_obj]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc]
  simp only [← comp_whiskerRight_assoc, hk]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  congr 3
  have hb := braiding_pairing hsymm' (P := P) (inv (BC.app K) ≫ q.map h)
    (Functor.LaxMonoidal.μ q (g.obj N') L ≫ q.map u)
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc] at hb ⊢
  exact hb

omit [MonoidalCategory 𝒴] [MonoidalCategory 𝒵] in
/-- The trace is natural in `K`: precomposing with `G (P_Z ◁ qZ k)` amounts to precomposing `h`
with `g k`. -/
lemma trace_naturality {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} {g : 𝒵 ⥤ 𝒴}
    (PFG : ∀ (A : 𝒱) (B : 𝒲), G.obj A ⊗ B ⟶ G.obj (A ⊗ Gs.obj B)) [∀ A B, IsIso (PFG A B)]
    (q : 𝒴 ⥤ 𝒲) (qZ : 𝒵 ⥤ 𝒱) (BC : g ⋙ q ⟶ qZ ⋙ G) [IsIso BC] (P : 𝒲) {PZ : 𝒱}
    (e : PZ ⟶ Gs.obj P)
    (hPFGl : ∀ {A A' : 𝒱} (f : A ⟶ A') (B : 𝒲),
      (G.map f ▷ B) ≫ PFG A' B = PFG A B ≫ G.map (f ▷ Gs.obj B))
    {K' K : 𝒵} (k : K' ⟶ K) {L : 𝒴} (h : g.obj K ⟶ L) :
    G.map (PZ ◁ qZ.map k) ≫ trace PFG q qZ BC P e K L h =
      trace PFG q qZ BC P e K' L (g.map k ≫ h) := by
  have hinvl {A A' : 𝒱} (f : A ⟶ A') (B : 𝒲) :
      G.map (f ▷ Gs.obj B) ≫ inv (PFG A' B) = inv (PFG A B) ≫ (G.map f ▷ B) := by
    rw [IsIso.eq_inv_comp, ← reassoc_of% (hPFGl f B), IsIso.hom_inv_id, Category.comp_id]
  have hBC : G.map (qZ.map k) ≫ inv (BC.app K) = inv (BC.app K') ≫ q.map (g.map k) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
    exact (BC.naturality k).symm
  unfold trace
  rw [← G.map_comp_assoc, BraidedCategory.braiding_naturality_right, G.map_comp_assoc,
    ← G.map_comp_assoc (qZ.map k ▷ PZ), ← whisker_exchange, G.map_comp_assoc, reassoc_of% hinvl,
    ← comp_whiskerRight_assoc, reassoc_of% hBC, Functor.map_comp]

end BaseChange

section Assembly

/-- The compatibility of the projection morphisms `pfg` of `g` and `pfG` of `G` with a base
change `BC : g ⋙ q ⟶ qZ ⋙ G` and the identification `θ : q ⋙ Gs ≅ gs ⋙ qZ`. -/
def PFBaseChange {𝒱 𝒲 𝒴 𝒵 : Type*} [Category 𝒱] [Category 𝒲] [Category 𝒴] [Category 𝒵]
    [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [MonoidalCategory 𝒴] [MonoidalCategory 𝒵]
    {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} {g : 𝒵 ⥤ 𝒴} {gs : 𝒴 ⥤ 𝒵}
    (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal]
    (BC : g ⋙ q ⟶ qZ ⋙ G) (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (pfg : curriedTensorInsertFunctor₁ g ⟶
      curriedTensorPost g ⋙ (Functor.whiskeringLeft 𝒴 𝒵 𝒴).obj gs)
    (pfG : curriedTensorInsertFunctor₁ G ⟶
      curriedTensorPost G ⋙ (Functor.whiskeringLeft 𝒲 𝒱 𝒲).obj Gs) : Prop :=
  ∀ A B, q.map ((pfg.app A).app B) ≫ BC.app (A ⊗ gs.obj B) ≫
    G.map (δ qZ A (gs.obj B)) ≫ G.map (qZ.obj A ◁ θ.inv.app B) =
      δ q (g.obj A) B ≫ (BC.app A ▷ q.obj B) ≫ (pfG.app (qZ.obj A)).app (q.obj B)

/-- **Projection morphisms of adjunctions are compatible with base change**: if the projection
morphisms `pfg` of `gs ⊣ g` and `pfG` of `Gs ⊣ G` are those of the adjunctions (characterised by
the counits, `hcg` and `hcG`), the base change `BC` is the mate of `θ` (`hmate`) and
`θ : q ⋙ Gs ≅ gs ⋙ qZ` is compatible with the comultiplications (`hθ`), then `PFBaseChange`
holds, that is the square
```
q (g A ⊗ B) ──q PF_g──▶ q g (A ⊗ gs B) ──BC──▶ G qZ (A ⊗ gs B) ──G δ──▶ G (qZ A ⊗ qZ gs B)
    │δ                                                                       │G (qZ A ◁ θ⁻¹)
    ▼                                                                       ▼
q g A ⊗ q B ──BC ▷ q B──▶ G qZ A ⊗ q B ─────────PF_G─────────▶ G (qZ A ⊗ Gs q B)
```
commutes: both composites are adjoint, for `Gs ⊣ G`, to the comultiplication of `q ⋙ Gs`
followed by `θ` and the counit of `gs ⊣ g` on the first factor. -/
lemma pfBaseChange_of_counit {𝒱 𝒲 𝒴 𝒵 : Type*} [Category 𝒱] [Category 𝒲] [Category 𝒴]
    [Category 𝒵] [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [MonoidalCategory 𝒴]
    [MonoidalCategory 𝒵] {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} [Gs.OplaxMonoidal] (aG : Gs ⊣ G)
    {g : 𝒵 ⥤ 𝒴} {gs : 𝒴 ⥤ 𝒵} [gs.OplaxMonoidal] (ag : gs ⊣ g)
    (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal]
    (BC : g ⋙ q ⟶ qZ ⋙ G) (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (pfg : curriedTensorInsertFunctor₁ g ⟶
      curriedTensorPost g ⋙ (Functor.whiskeringLeft 𝒴 𝒵 𝒴).obj gs)
    (pfG : curriedTensorInsertFunctor₁ G ⟶
      curriedTensorPost G ⋙ (Functor.whiskeringLeft 𝒲 𝒱 𝒲).obj Gs)
    (hcg : ∀ A B, gs.map ((pfg.app A).app B) ≫ ag.counit.app (A ⊗ gs.obj B) =
      δ gs (g.obj A) B ≫ (ag.counit.app A ▷ gs.obj B))
    (hcG : ∀ A B, Gs.map ((pfG.app A).app B) ≫ aG.counit.app (A ⊗ Gs.obj B) =
      δ Gs (G.obj A) B ≫ (aG.counit.app A ▷ Gs.obj B))
    (hmate : ∀ K, Gs.map (BC.app K) ≫ aG.counit.app (qZ.obj K) =
      θ.hom.app (g.obj K) ≫ qZ.map (ag.counit.app K))
    (hθ : ∀ A B, θ.hom.app (A ⊗ B) ≫ qZ.map (δ gs A B) ≫ δ qZ (gs.obj A) (gs.obj B) =
      Gs.map (δ q A B) ≫ δ Gs (q.obj A) (q.obj B) ≫ (θ.hom.app A ⊗ₘ θ.hom.app B)) :
    PFBaseChange q qZ BC θ pfg pfG := by
  intro A B
  apply (aG.homEquiv _ _).symm.injective
  have hθn : Gs.map (q.map ((pfg.app A).app B)) ≫ θ.hom.app (g.obj (A ⊗ gs.obj B)) =
      θ.hom.app (g.obj A ⊗ B) ≫ qZ.map (gs.map ((pfg.app A).app B)) :=
    θ.hom.naturality ((pfg.app A).app B)
  have hG : Gs.map ((pfG.app (qZ.obj A)).app (q.obj B)) ≫
      aG.counit.app (qZ.obj A ⊗ Gs.obj (q.obj B)) =
      δ Gs (G.obj (qZ.obj A)) (q.obj B) ≫ (aG.counit.app (qZ.obj A) ▷ Gs.obj (q.obj B)) :=
    hcG _ _
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [Adjunction.counit_naturality, Adjunction.counit_naturality_assoc, reassoc_of% (hmate _),
    reassoc_of% hθn, ← qZ.map_comp_assoc, hcg, qZ.map_comp_assoc]
  erw [hG]
  erw [← δ_natural_left_assoc qZ (ag.counit.app A) (gs.obj B)]
  erw [← δ_natural_left_assoc Gs (BC.app A) (q.obj B)]
  erw [reassoc_of% (hθ (g.obj A) B)]
  congr 2
  erw [← comp_whiskerRight (Gs.map (BC.app A)), hmate]
  rw [tensorHom_def_assoc, whisker_exchange_assoc]
  dsimp only [Functor.id_obj]
  rw [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_app]
  erw [MonoidalCategory.whiskerLeft_id]
  rw [Category.comp_id, comp_whiskerRight]

open MonoidalClosed

variable {𝒱 𝒲 𝒴 𝒵 : Type*} [Category 𝒱] [Category 𝒲] [Category 𝒴] [Category 𝒵]
  [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [MonoidalCategory 𝒴] [MonoidalCategory 𝒵]
  [BraidedCategory 𝒱] [BraidedCategory 𝒲]
  [MonoidalClosed 𝒱] [MonoidalClosed 𝒲] [MonoidalClosed 𝒴] [MonoidalClosed 𝒵]

omit [BraidedCategory 𝒱] [BraidedCategory 𝒲] [MonoidalClosed 𝒲] in
/-- The pairing of the Verdier exchange morphism (`Verdier.exchangePairing`), precomposed with
`G A ◁ G x`, is the projection morphism, the counit and `G` of the transpose of `x`. -/
lemma exchangePairing_whiskerLeft {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} (aG : Gs ⊣ G) {Gu : 𝒲 ⥤ 𝒱}
    (aGu : G ⊣ Gu)
    (pfG : curriedTensorInsertFunctor₁ G ⟶
      curriedTensorPost G ⋙ (Functor.whiskeringLeft 𝒲 𝒱 𝒲).obj Gs)
    (A : 𝒱) {Sz : 𝒱} {L : 𝒲} (x : Sz ⟶ (ihom A).obj (Gu.obj L)) :
    (G.obj A ◁ G.map x) ≫ Verdier.exchangePairing aG aGu pfG A L =
      (pfG.app A).app (G.obj Sz) ≫ G.map (A ◁ aG.counit.app Sz) ≫ G.map (uncurry x) ≫
        aGu.counit.app L := by
  unfold Verdier.exchangePairing
  rw [Verdier.pf_naturality_right_assoc]
  simp only [← G.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, uncurry_eq]
  simp

/-- **The Künneth–Verdier pairings and the trace.** For a cartesian square with `G` and `g` proper,
the Künneth–Verdier morphism of `(P, g N')` (the transpose of the pairing with `αY`), precomposed
with the trace of the absolute Verdier exchange of `g` at `N'`, is `G` of the Künneth–Verdier
morphism of `(P_Z, N')`, followed by the identification `eT`, the Verdier exchange of `G` and the
base change of `q (g N')`; the hypothesis `hstar` is the functoriality of `α` along `G`. Writing
`κ_Y : P ⊗ q [g N', ω_Y] ⟶ [q g N', T]` and `κ_Z : P_Z ⊗ qZ [N', ω_Z] ⟶ [qZ N', T_Z]` for
the Künneth–Verdier morphisms, the square
```
G (P_Z ⊗ qZ [N', ω_Z]) ──G κ_Z──▶ G [qZ N', T_Z] ──G [_, eT]──▶ G [qZ N', Gu T]
        │trace                                                     │Verdier exchange of G
        ▼                                                          ▼
P ⊗ q [g N', ω_Y] ───────κ_Y──────▶ [q g N', T] ◀──[BC, T]── [G qZ N', T]
```
commutes. -/
lemma trace_comp_curry {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} [Gs.OplaxMonoidal] (aG : Gs ⊣ G) {Gu : 𝒲 ⥤ 𝒱}
    (aGu : G ⊣ Gu)
    (pfG : curriedTensorInsertFunctor₁ G ⟶
      curriedTensorPost G ⋙ (Functor.whiskeringLeft 𝒲 𝒱 𝒲).obj Gs)
    [∀ A B, IsIso ((pfG.app A).app B)]
    (hcG : ∀ A B, Gs.map ((pfG.app A).app B) ≫ aG.counit.app (A ⊗ Gs.obj B) =
      δ Gs (G.obj A) B ≫ (aG.counit.app A ▷ Gs.obj B))
    {g : 𝒵 ⥤ 𝒴} {gs : 𝒴 ⥤ 𝒵} (ag : gs ⊣ g) {gu : 𝒴 ⥤ 𝒵} (agu : g ⊣ gu)
    (pfg : curriedTensorInsertFunctor₁ g ⟶
      curriedTensorPost g ⋙ (Functor.whiskeringLeft 𝒴 𝒵 𝒴).obj gs)
    (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal]
    (BC : g ⋙ q ⟶ qZ ⋙ G) [IsIso BC] (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (hmate : ∀ K, Gs.map (BC.app K) ≫ aG.counit.app (qZ.obj K) =
      θ.hom.app (g.obj K) ≫ qZ.map (ag.counit.app K))
    (hPF2 : PFBaseChange q qZ BC θ pfg pfG)
    (hsymm : ∀ X Y : 𝒱, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (hsymm' : ∀ X Y : 𝒲, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (P : 𝒲) {PZ : 𝒱} (e : PZ ⟶ Gs.obj P) {ωY : 𝒴} {ωZ : 𝒵} (d : gu.obj ωY ≅ ωZ)
    {T : 𝒲} {TZ : 𝒱} (αY : P ⊗ q.obj ωY ⟶ T) (αZ : PZ ⊗ qZ.obj ωZ ⟶ TZ) (eT : TZ ⟶ Gu.obj T)
    (hstar : G.map (αZ ≫ eT) ≫ aGu.counit.app T =
      trace (fun A B ↦ (pfG.app A).app B) q qZ BC P e ωZ ωY
        (g.map d.inv ≫ agu.counit.app ωY) ≫ αY)
    (N' : 𝒵) :
    trace (fun A B ↦ (pfG.app A).app B) q qZ BC P e ((ihom N').obj ωZ)
        ((ihom (g.obj N')).obj ωY) (Verdier.absoluteExchange ag agu pfg ωZ ωY d N') ≫
      curry ((α_ _ _ _).inv ≫ ((β_ (q.obj (g.obj N')) P).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (P ◁ Functor.LaxMonoidal.μ q (g.obj N') ((ihom (g.obj N')).obj ωY)) ≫
        (P ◁ q.map ((ihom.ev (g.obj N')).app ωY)) ≫ αY) =
    G.map (curry ((α_ _ _ _).inv ≫ ((β_ (qZ.obj N') PZ).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (PZ ◁ Functor.LaxMonoidal.μ qZ N' ((ihom N').obj ωZ)) ≫
        (PZ ◁ qZ.map ((ihom.ev N').app ωZ)) ≫ αZ)) ≫
      G.map ((ihom (qZ.obj N')).map eT) ≫ Verdier.exchange aG aGu pfG (qZ.obj N') T ≫
      (pre (BC.app N')).app T := by
  have hPFGr : ∀ A {B B' : 𝒲} (f : B ⟶ B'), G.obj A ◁ f ≫ (pfG.app A).app B' =
      (pfG.app A).app B ≫ G.map (A ◁ Gs.map f) := fun A _ _ f ↦ Verdier.pf_naturality_right pfG A f
  have hPFGl : ∀ {A A' : 𝒱} (f : A ⟶ A') (B : 𝒲),
      (G.map f ▷ B) ≫ (pfG.app A').app B = (pfG.app A).app B ≫ G.map (f ▷ Gs.obj B) := by
    intro A A' f B
    have := NatTrans.congr_app (pfG.naturality f) B
    dsimp at this
    exact this
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry]
  conv_rhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc, uncurry_pre_app,
    Category.assoc, Category.assoc, uncurry_natural_left, uncurry_natural_left,
    Verdier.uncurry_exchange]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← G.map_comp,
    exchangePairing_whiskerLeft aG aGu pfG, uncurry_natural_right, uncurry_curry]
  have hu : g.obj N' ◁ Verdier.absoluteExchange ag agu pfg ωZ ωY d N' ≫
      (ihom.ev (g.obj N')).app ωY = (pfg.app N').app (g.obj ((ihom N').obj ωZ)) ≫
        g.map (N' ◁ ag.counit.app ((ihom N').obj ωZ)) ≫
        (g.map ((ihom.ev N').app ωZ) ≫ g.map d.inv ≫ agu.counit.app ωY) := by
    rw [← uncurry_eq, Verdier.absoluteExchange, uncurry_natural_left, Verdier.uncurry_exchange,
      exchangePairing_whiskerLeft ag agu pfg, uncurry_ihom_map, g.map_comp, Category.assoc]
  have hci := whiskerLeft_trace_pairing aG (fun A B ↦ (pfG.app A).app B) hcG ag q qZ BC θ hmate
    (fun A B ↦ (pfg.app A).app B) hPF2 hPFGr P e hsymm hsymm' hPFGl N' ((ihom N').obj ωZ)
    (Verdier.absoluteExchange ag agu pfg ωZ ωY d N') ((ihom.ev (g.obj N')).app ωY)
    (g.map ((ihom.ev N').app ωZ) ≫ g.map d.inv ≫ agu.counit.app ωY) hu
  have hnat := trace_naturality (PFG := fun A B ↦ (pfG.app A).app B) (q := q) (qZ := qZ)
    (BC := BC) (P := P) (e := e) hPFGl
    ((ihom.ev N').app ωZ) (g.map d.inv ≫ agu.counit.app ωY)
  dsimp only [Functor.comp_obj, Functor.id_obj, curriedTensor_obj_obj] at hnat
  rw [reassoc_of% hci, ← hnat]
  simp only [Category.assoc, Functor.map_comp]
  rw [← G.map_comp_assoc αZ eT, hstar]

end Assembly

section Mate

variable {𝒱 𝒲 𝒴 𝒵 : Type*} [Category 𝒱] [Category 𝒲] [Category 𝒴] [Category 𝒵]

/-- The counit form of the compatibility of a base change with adjunctions `gs ⊣ g`,
`Gs ⊣ G`, deduced from its unit form. -/
lemma counit_mate_of_unit {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} (aG : Gs ⊣ G) {g : 𝒵 ⥤ 𝒴}
    {gs : 𝒴 ⥤ 𝒵} (ag : gs ⊣ g) (q : 𝒴 ⥤ 𝒲) (qZ : 𝒵 ⥤ 𝒱) (BC : g ⋙ q ⟶ qZ ⋙ G)
    (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (hunit : ∀ M, q.map (ag.unit.app M) ≫ BC.app (gs.obj M) =
      aG.unit.app (q.obj M) ≫ G.map (θ.hom.app M)) (K : 𝒵) :
    Gs.map (BC.app K) ≫ aG.counit.app (qZ.obj K) =
      θ.hom.app (g.obj K) ≫ qZ.map (ag.counit.app K) := by
  apply (aG.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    Adjunction.unit_naturality_assoc]
  dsimp only [Functor.comp_obj]
  rw [Adjunction.right_triangle_components, Category.comp_id,
    Functor.map_comp, ← reassoc_of% (hunit (g.obj K))]
  have hn := BC.naturality (ag.counit.app K)
  dsimp at hn
  rw [← hn, ← q.map_comp_assoc, Adjunction.right_triangle_components, q.map_id, Category.id_comp]

end Mate

section Iff

open MonoidalClosed

variable {𝒱 𝒲 𝒴 𝒵 : Type*} [Category 𝒱] [Category 𝒲] [Category 𝒴] [Category 𝒵]
  [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [MonoidalCategory 𝒴] [MonoidalCategory 𝒵]
  [BraidedCategory 𝒱] [BraidedCategory 𝒲]
  [MonoidalClosed 𝒱] [MonoidalClosed 𝒲] [MonoidalClosed 𝒴] [MonoidalClosed 𝒵]

omit [MonoidalCategory 𝒴] [MonoidalCategory 𝒵] [MonoidalClosed 𝒱] [MonoidalClosed 𝒲]
  [MonoidalClosed 𝒴] [MonoidalClosed 𝒵] in
/-- The trace of an isomorphism is an isomorphism. -/
lemma isIso_trace {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} {g : 𝒵 ⥤ 𝒴}
    (PFG : ∀ (A : 𝒱) (B : 𝒲), G.obj A ⊗ B ⟶ G.obj (A ⊗ Gs.obj B)) [∀ A B, IsIso (PFG A B)]
    (q : 𝒴 ⥤ 𝒲) (qZ : 𝒵 ⥤ 𝒱) (BC : g ⋙ q ⟶ qZ ⋙ G) [IsIso BC] (P : 𝒲) {PZ : 𝒱}
    (e : PZ ⟶ Gs.obj P) [IsIso e] (K : 𝒵) (L : 𝒴) (h : g.obj K ⟶ L) [IsIso h] :
    IsIso (trace PFG q qZ BC P e K L h) := by
  unfold trace
  infer_instance

/-- Under the hypotheses of `trace_comp_curry`, with the projection morphisms and the
identifications invertible, the Künneth–Verdier morphism of `(P, g N')` is an isomorphism if and
only if `G` of that of `(P_Z, N')` is. -/
lemma isIso_curry_iff {G : 𝒱 ⥤ 𝒲} {Gs : 𝒲 ⥤ 𝒱} [Gs.OplaxMonoidal] (aG : Gs ⊣ G) {Gu : 𝒲 ⥤ 𝒱}
    (aGu : G ⊣ Gu)
    (pfG : curriedTensorInsertFunctor₁ G ⟶
      curriedTensorPost G ⋙ (Functor.whiskeringLeft 𝒲 𝒱 𝒲).obj Gs)
    [∀ A B, IsIso ((pfG.app A).app B)]
    (hcG : ∀ A B, Gs.map ((pfG.app A).app B) ≫ aG.counit.app (A ⊗ Gs.obj B) =
      δ Gs (G.obj A) B ≫ (aG.counit.app A ▷ Gs.obj B))
    {g : 𝒵 ⥤ 𝒴} {gs : 𝒴 ⥤ 𝒵} (ag : gs ⊣ g) {gu : 𝒴 ⥤ 𝒵} (agu : g ⊣ gu)
    (pfg : curriedTensorInsertFunctor₁ g ⟶
      curriedTensorPost g ⋙ (Functor.whiskeringLeft 𝒴 𝒵 𝒴).obj gs)
    (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal]
    (BC : g ⋙ q ⟶ qZ ⋙ G) [IsIso BC] (θ : q ⋙ Gs ≅ gs ⋙ qZ)
    (hmate : ∀ K, Gs.map (BC.app K) ≫ aG.counit.app (qZ.obj K) =
      θ.hom.app (g.obj K) ≫ qZ.map (ag.counit.app K))
    (hPF2 : PFBaseChange q qZ BC θ pfg pfG)
    (hsymm : ∀ X Y : 𝒱, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (hsymm' : ∀ X Y : 𝒲, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (P : 𝒲) {PZ : 𝒱} (e : PZ ⟶ Gs.obj P) {ωY : 𝒴} {ωZ : 𝒵} (d : gu.obj ωY ≅ ωZ)
    {T : 𝒲} {TZ : 𝒱} (αY : P ⊗ q.obj ωY ⟶ T) (αZ : PZ ⊗ qZ.obj ωZ ⟶ TZ) (eT : TZ ⟶ Gu.obj T)
    [IsIso e] [∀ A B, IsIso ((pfg.app A).app B)] [IsIso eT]
    (hstar : G.map (αZ ≫ eT) ≫ aGu.counit.app T =
      trace (fun A B ↦ (pfG.app A).app B) q qZ BC P e ωZ ωY
        (g.map d.inv ≫ agu.counit.app ωY) ≫ αY)
    (N' : 𝒵) :
    IsIso (curry ((α_ _ _ _).inv ≫ ((β_ (q.obj (g.obj N')) P).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (P ◁ Functor.LaxMonoidal.μ q (g.obj N') ((ihom (g.obj N')).obj ωY)) ≫
        (P ◁ q.map ((ihom.ev (g.obj N')).app ωY)) ≫ αY)) ↔
    IsIso (G.map (curry ((α_ _ _ _).inv ≫ ((β_ (qZ.obj N') PZ).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (PZ ◁ Functor.LaxMonoidal.μ qZ N' ((ihom N').obj ωZ)) ≫
        (PZ ◁ qZ.map ((ihom.ev N').app ωZ)) ≫ αZ))) := by
  have h := trace_comp_curry aG aGu pfG hcG ag agu pfg q qZ BC θ hmate hPF2 hsymm hsymm' P e d αY αZ
    eT hstar N'
  have : IsIso (Verdier.exchange ag agu pfg N' ωY) := Verdier.isIso_exchange_of_isIso _ _ _ _ _
  have : IsIso (Verdier.exchange aG aGu pfG (qZ.obj N') T) :=
    Verdier.isIso_exchange_of_isIso _ _ _ _ _
  have : IsIso ((pre (BC.app N')).app T) := isIso_pre_app _ _
  have : IsIso (Verdier.absoluteExchange ag agu pfg ωZ ωY d N') := by
    unfold Verdier.absoluteExchange
    infer_instance
  have : IsIso (trace (fun A B ↦ (pfG.app A).app B) q qZ BC P e ((ihom N').obj ωZ)
      ((ihom (g.obj N')).obj ωY) (Verdier.absoluteExchange ag agu pfg ωZ ωY d N')) :=
    isIso_trace _ _ _ _ _ _ _ _ _
  constructor
  · intro hY
    have : IsIso (G.map (curry ((α_ _ _ _).inv ≫ ((β_ (qZ.obj N') PZ).hom ▷ _) ≫
        (α_ _ _ _).hom ≫ (PZ ◁ Functor.LaxMonoidal.μ qZ N' ((ihom N').obj ωZ)) ≫
        (PZ ◁ qZ.map ((ihom.ev N').app ωZ)) ≫ αZ)) ≫ G.map ((ihom (qZ.obj N')).map eT) ≫
        Verdier.exchange aG aGu pfG (qZ.obj N') T ≫ (pre (BC.app N')).app T) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map ((ihom (qZ.obj N')).map eT) ≫
        Verdier.exchange aG aGu pfG (qZ.obj N') T ≫ (pre (BC.app N')).app T)
  · intro hZ
    have : IsIso (trace (fun A B ↦ (pfG.app A).app B) q qZ BC P e ((ihom N').obj ωZ)
        ((ihom (g.obj N')).obj ωY) (Verdier.absoluteExchange ag agu pfg ωZ ωY d N') ≫
      curry ((α_ _ _ _).inv ≫ ((β_ (q.obj (g.obj N')) P).hom ▷ _) ≫ (α_ _ _ _).hom ≫
        (P ◁ Functor.LaxMonoidal.μ q (g.obj N') ((ihom (g.obj N')).obj ωY)) ≫
        (P ◁ q.map ((ihom.ev (g.obj N')).app ωY)) ≫ αY)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (trace (fun A B ↦ (pfG.app A).app B) q qZ BC P e
      ((ihom N').obj ωZ) ((ihom (g.obj N')).obj ωY)
      (Verdier.absoluteExchange ag agu pfg ωZ ωY d N')) _
end Iff

end CategoryTheory.ProjectionBaseChange
