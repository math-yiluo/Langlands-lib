/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.Sieves.Basic
public import Mathlib.CategoryTheory.Sites.Sieves.Functoriality
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
public import Mathlib.CategoryTheory.Sites.Sieves.Presieve
public import Mathlib.CategoryTheory.Sites.Sieves.Shrink
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Reindexing a finite presieve in a filtered colimit

Source: Stacks Project, Sites, Tag 09YL, finite-diagram observation.
(blueprint: lem-weil-pbc-colimit-presieve-indexed-presentation)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem finite_equalities
    {J : Type u} [SmallCategory J] [IsFiltered J] (G : J ⥤ Type u)
    (c : Cocone G) (hc : IsColimit c) {ι : Type u} [Finite ι] (j : J)
    (x y : ι → G.obj j) (h : ∀ i, c.ι.app j (x i) = c.ι.app j (y i)) :
    ∃ (k : J) (e : j ⟶ k), ∀ i, G.map e (x i) = G.map e (y i) := by
  classical
  choose k e he using fun i => (Types.FilteredColimit.isColimit_eq_iff' hc _ _).mp (h i)
  obtain ⟨l, d, g, hg⟩ := IsFiltered.wideSpan e
  refine ⟨l, d, fun i => ?_⟩
  rw [← hg i]
  simpa only [G.map_comp, ConcreteCategory.comp_apply] using congrArg (G.map (g i)) (he i)

private theorem image_comparisons
    {C D : Type u} [SmallCategory C] [SmallCategory D] (G : C ⥤ D)
    {U : C} (R : Presieve U) {S : D} (h : G.obj U = S)
    {τ : Type u} {X : τ → D} (f : ∀ t, X t ⟶ S)
    (hR : h ▸ R.map G = Presieve.ofArrows X f) :
    (∀ t, ∃ q : R.uncurry, Arrow.mk (G.map q.1.2) = Arrow.mk (f t)) ∧
    (∀ q : R.uncurry, ∃ t, Arrow.mk (G.map q.1.2) = Arrow.mk (f t)) := by
  cases h
  dsimp only at hR
  constructor
  · intro t
    have hm : R.map G (f t) := by rw [hR]; exact Presieve.ofArrows.mk t
    obtain ⟨Z, hz, g, hg, heq⟩ := Presieve.map_iff.mp hm
    refine ⟨⟨⟨Z, g⟩, hg⟩, ?_⟩
    rw [heq]
    exact Arrow.arrow_mk_eqToHom_comp _ hz
  · intro q
    have hm : Presieve.ofArrows X f (G.map q.1.2) := by
      rw [← hR]
      exact Presieve.map_map q.2
    obtain ⟨t, ht, heq⟩ := Presieve.ofArrows_surj _ _ hm
    refine ⟨t, ?_⟩
    rw [heq]
    exact Arrow.arrow_mk_eqToHom_comp _ ht.symm

private theorem presieve_mem_of_arrow_eq
    {C : Type u} [SmallCategory C] {U Y Z : C} (R : Presieve U)
    {a : Y ⟶ U} {b : Z ⟶ U} (h : Arrow.mk a = Arrow.mk b) (hb : R b) : R a := by
  obtain ⟨hs, _, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  subst Z
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hh
  exact hh.symm ▸ hb

private theorem presieve_eq_of_comparisons
    {C D : Type u} [SmallCategory C] [SmallCategory D] (G : C ⥤ D)
    {U : C} (R : Presieve U) {τ : Type u} (p : τ → R.uncurry)
    (h : ∀ q : R.uncurry, ∃ t,
      Arrow.mk (G.map q.1.2) = Arrow.mk (G.map (p t).1.2)) :
    R.map G = Presieve.ofArrows (fun t => G.obj (p t).1.1)
      (fun t => G.map (p t).1.2) := by
  apply le_antisymm
  · intro Z g hg
    cases hg with
    | @of Y g hg =>
      obtain ⟨t, ht⟩ := h ⟨⟨Y, g⟩, hg⟩
      exact presieve_mem_of_arrow_eq _ ht (Presieve.ofArrows.mk t)
  · intro Z g hg
    cases hg with
    | mk t => exact Presieve.map_map (p t).2

private theorem ofArrows_transport
    {C : Type u} [SmallCategory C] {U W : C} (h : U = W)
    {τ : Type u} (X : τ → C) (f : ∀ t, X t ⟶ U) :
    Presieve.ofArrows X (fun t => f t ≫ eqToHom h) = h ▸ Presieve.ofArrows X f := by
  cases h
  simp

/-- A finite stage presieve can eventually be presented by any finite indexing of its image.
Source: Stacks Project, Sites, Tag 09YL, finite-diagram observation and axiom (2).
(blueprint: lem-weil-pbc-colimit-presieve-indexed-presentation)

Proof: For each requested index choose a member of the original presieve with that image.
Conversely, choose an index for every original member. Each member and the representative
chosen for its index have equal cocone images. Eventual equality in the arrow colimit and
a finite wide span identify all these pairs at one successor. The chosen arrows therefore
generate exactly the image of the original presieve. Next align its target with the fixed
stage target by eventual equality in the object colimit. Move all arrows to this common
successor and postcompose with the equality morphism of targets. Their presieve is the
transported transition image; cocone naturality preserves the requested arrow images.
An empty indexing forces the presieve to be empty, and only target alignment is needed.
Repeated indices impose finite comparisons, not injectivity. -/
theorem colimit_presieve_indexed_presentation
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j₀ k₀ : J) (T₀ : F.obj j₀) (U₀ : F.obj k₀) (R₀ : Presieve U₀)
    [Finite R₀.uncurry] {S : V.pt}
    (hT : (V.ι.app j₀).toFunctor.obj T₀ = S)
    (hU : (V.ι.app k₀).toFunctor.obj U₀ = S)
    {τ : Type u} [Finite τ] {X : τ → V.pt} (f : ∀ t, X t ⟶ S)
    (hR : hU ▸ R₀.map (V.ι.app k₀).toFunctor = Presieve.ofArrows X f) :
    ∃ (j : J) (e : j₀ ⟶ j) (d : k₀ ⟶ j)
      (h : (F.map d).toFunctor.obj U₀ = (F.map e).toFunctor.obj T₀)
      (A : τ → F.obj j) (a : ∀ t, A t ⟶ (F.map e).toFunctor.obj T₀),
      Presieve.ofArrows A a = h ▸ R₀.map (F.map d).toFunctor ∧
      ∀ t, Arrow.mk ((V.ι.app j).toFunctor.map (a t)) = Arrow.mk (f t) := by
  classical
  obtain ⟨hp, hq⟩ := image_comparisons (V.ι.app k₀).toFunctor R₀ hU f hR
  choose p hp using hp
  choose t ht using hq
  have hc (q : R₀.uncurry) :
      (Cat.arrows.mapCocone V).ι.app k₀ (Arrow.mk q.1.2) =
        (Cat.arrows.mapCocone V).ι.app k₀ (Arrow.mk (p (t q)).1.2) :=
    (ht q).trans (hp (t q)).symm
  obtain ⟨k, d, hd⟩ := finite_equalities (F ⋙ Cat.arrows)
    (Cat.arrows.mapCocone V) harrows k₀
    (fun q : R₀.uncurry => Arrow.mk q.1.2)
    (fun q => Arrow.mk (p (t q)).1.2) hc
  have hUk : (V.ι.app k).toFunctor.obj ((F.map d).toFunctor.obj U₀) = S :=
    (congrArg (fun H : F.obj k₀ ⟶ V.pt => H.toFunctor.obj U₀) (V.w d)).trans hU
  obtain ⟨j, e, g, hg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (F ⋙ Cat.objects) hobjects).mp
      (hT.trans hUk.symm)
  change (F.map e).toFunctor.obj T₀ =
    (F.map g).toFunctor.obj ((F.map d).toFunctor.obj U₀) at hg
  have hcomp : (F.map (d ≫ g)).toFunctor =
      (F.map d).toFunctor ⋙ (F.map g).toFunctor :=
    congrArg Cat.Hom.toFunctor (F.map_comp d g)
  have h : (F.map (d ≫ g)).toFunctor.obj U₀ = (F.map e).toFunctor.obj T₀ := by
    rw [hcomp]
    exact hg.symm
  refine ⟨j, e, d ≫ g, h,
    fun t => (F.map (d ≫ g)).toFunctor.obj (p t).1.1,
    fun t => (F.map (d ≫ g)).toFunctor.map (p t).1.2 ≫ eqToHom h, ?_, ?_⟩
  · have heq' : R₀.map (F.map (d ≫ g)).toFunctor =
        Presieve.ofArrows (fun t => (F.map (d ≫ g)).toFunctor.obj (p t).1.1)
          (fun t => (F.map (d ≫ g)).toFunctor.map (p t).1.2) := by
      apply presieve_eq_of_comparisons _ R₀ p
      intro q
      refine ⟨t q, ?_⟩
      have hdq : Arrow.mk ((F.map d).toFunctor.map q.1.2) =
          Arrow.mk ((F.map d).toFunctor.map (p (t q)).1.2) := hd q
      have hh := congrArg (F.map g).toFunctor.mapArrow.obj hdq
      rw [hcomp]
      exact hh
    rw [heq']
    exact ofArrows_transport h _ _
  · intro t
    calc
      Arrow.mk ((V.ι.app j).toFunctor.map
          ((F.map (d ≫ g)).toFunctor.map (p t).1.2 ≫ eqToHom h)) =
          Arrow.mk ((V.ι.app j).toFunctor.map
            ((F.map (d ≫ g)).toFunctor.map (p t).1.2)) := by
        simp only [Functor.map_comp, eqToHom_map, Arrow.arrow_mk_comp_eqToHom]
      _ = Arrow.mk ((V.ι.app k₀).toFunctor.map (p t).1.2) :=
        congrArg (fun H : F.obj k₀ ⟶ V.pt => Arrow.mk (H.toFunctor.map (p t).1.2))
          (V.w (d ≫ g))
      _ = Arrow.mk (f t) := hp t

end CategoryTheory
