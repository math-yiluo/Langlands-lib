/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Basic.Finite.Prod
import Mathlib.Tactic.FinCases

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Finitely many equalities in a set colimit hold after one transition. -/
private theorem finite_stage_eq
    {J : Type u} [SmallCategory J] [IsFiltered J] (G : J ⥤ Type u)
    (c : Cocone G) (hc : IsColimit c) {α : Type u} [Finite α]
    (j : J) (x y : α → G.obj j) (h : ∀ a, c.ι.app j (x a) = c.ι.app j (y a)) :
    ∃ (k : J) (f : j ⟶ k), ∀ a, G.map f (x a) = G.map f (y a) := by
  classical
  choose k f hf using fun a => (Types.FilteredColimit.isColimit_eq_iff' hc _ _).mp (h a)
  obtain ⟨l, g, r, hr⟩ := IsFiltered.wideSpan f
  refine ⟨l, g, fun a => ?_⟩
  simpa only [← ConcreteCategory.comp_apply, ← G.map_comp, hr a] using
    congrArg (fun z => G.map (r a) z) (hf a)

/-- Finite representatives can be chosen at a stage above any prescribed stage. -/
private theorem finite_representatives_above
    {J : Type u} [SmallCategory J] [IsFiltered J] (G : J ⥤ Type u)
    (c : Cocone G) (hc : IsColimit c) {α : Type u} [Finite α]
    (j : J) (x : α → c.pt) :
    ∃ (k : J) (_f : j ⟶ k) (y : α → G.obj k), ∀ a, c.ι.app k (y a) = x a := by
  classical
  choose k y hy using fun a => Types.jointly_surjective_of_isColimit hc (x a)
  let f := fun a => IsFiltered.leftToMax j (k a)
  let g := fun a => IsFiltered.rightToMax j (k a)
  obtain ⟨t, r, s, _⟩ := IsFiltered.wideSpan f
  refine ⟨t, r, fun a => G.map (g a ≫ s a) (y a), fun a => ?_⟩
  exact (ConcreteCategory.congr_hom (c.w (g a ≫ s a)) (y a)).trans (hy a)

/-- Equal arrows give equal composites, including transported middle endpoints. -/
private theorem arrow_comp_congr {C : Type u} [Category.{u} C]
    {a b c d : Arrow C} (ha : a = c) (hb : b = d)
    (h : a.right = b.left) (h' : c.right = d.left) :
    Arrow.mk (a.hom ≫ eqToHom h ≫ b.hom) =
      Arrow.mk (c.hom ≫ eqToHom h' ≫ d.hom) := by
  subst c
  subst d
  rfl

/-- Finitely many isomorphisms out of fixed stage objects lift above that stage.
Source: Stacks Project, Sites, Tag 09YL, finite-diagram observation, and Categories,
Tag 04AX, the object and arrow description of filtered colimits.
(blueprint: lem-weil-pbc-filtered-colimit-finite-iso-lift)

Proof: Represent the hom and inverse arrows of each E i by surjectivity of the
arrow cocone. Move this finite family above j using maxima and IsFiltered.wideSpan.
The images of the inverse targets and hom sources equal the images of D i, and
the hom targets and inverse sources have equal images. Apply eventual equality
in the object colimit to these three endpoint equations for each i, synchronizing
all transitions with wideSpan. Transport the arrows along the resulting equalities.
Cocone naturality preserves their Arrow images, including endpoints. Consequently
their composites have the same Arrow images as identities. Eventual equality in
the arrow colimit, again synchronized with wideSpan, makes both inverse equations
hold at one refinement. They define isomorphisms; transport the codomains along
F.map_comp to the images under the composite transition out of j. Naturality gives
the required Arrow images. The finite-family constructions also work for an empty
index, since wideSpan has the given stage as its source. No stage category needs
to be finite. -/
theorem filteredColimit_finite_iso_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    {ι : Type u} [Finite ι] (j : J) (D : ι → F.obj j) (Z : ι → V.pt)
    (E : ∀ i, (V.ι.app j).toFunctor.obj (D i) ≅ Z i) :
    ∃ (k : J) (c : j ⟶ k) (D' : ι → F.obj k)
      (t : ∀ i, D' i ≅ (F.map c).toFunctor.obj (D i)),
      ∀ i, Arrow.mk ((V.ι.app k).toFunctor.map (t i).hom) = Arrow.mk (E i).inv := by
  classical
  let R : ι × Bool → Arrow V.pt := fun p =>
    if p.2 then Arrow.mk (E p.1).hom else Arrow.mk (E p.1).inv
  obtain ⟨k, c, A, hA⟩ := finite_representatives_above (F ⋙ Cat.arrows)
    (Cat.arrows.mapCocone V) harrows j R
  let B := fun i => A (i, false)
  let C := fun i => A (i, true)
  have hB (i : ι) : Arrow.mk ((V.ι.app k).toFunctor.map (B i).hom) =
      Arrow.mk (E i).inv := hA (i, false)
  have hC (i : ι) : Arrow.mk ((V.ι.app k).toFunctor.map (C i).hom) =
      Arrow.mk (E i).hom := hA (i, true)
  let T := fun i => (F.map c).toFunctor.obj (D i)
  have hT (i : ι) : (V.ι.app k).toFunctor.obj (T i) =
      (V.ι.app j).toFunctor.obj (D i) :=
    congrArg (fun W : F.obj j ⟶ V.pt => W.toFunctor.obj (D i)) (V.w c)
  let X : ι × Fin 3 → F.obj k := fun p =>
    ![(B p.1).right, (C p.1).left, (C p.1).right] p.2
  let Y : ι × Fin 3 → F.obj k := fun p => ![T p.1, T p.1, (B p.1).left] p.2
  have hXY (p : ι × Fin 3) : (V.ι.app k).toFunctor.obj (X p) =
      (V.ι.app k).toFunctor.obj (Y p) := by
    rcases p with ⟨i, q⟩
    fin_cases q
    · exact (congrArg Arrow.right (hB i)).trans (hT i).symm
    · exact (congrArg Arrow.left (hC i)).trans (hT i).symm
    · exact (congrArg Arrow.right (hC i)).trans (congrArg Arrow.left (hB i)).symm
  obtain ⟨l, r, hr⟩ := finite_stage_eq (F ⋙ Cat.objects)
    (Cat.objects.mapCocone V) hobjects k X Y hXY
  let W := (F.map r).toFunctor
  let B' := fun i => W.mapArrow.obj (B i)
  let C' := fun i => W.mapArrow.obj (C i)
  have h₀ (i : ι) : (B' i).right = W.obj (T i) := hr (i, 0)
  have h₁ (i : ι) : (C' i).left = W.obj (T i) := hr (i, 1)
  have h₂ (i : ι) : (C' i).right = (B' i).left := hr (i, 2)
  let f := fun i => (B' i).hom ≫ eqToHom (h₀ i)
  let g := fun i => eqToHom (h₁ i).symm ≫ (C' i).hom ≫ eqToHom (h₂ i)
  have hf (i : ι) : Arrow.mk ((V.ι.app l).toFunctor.map (f i)) =
      Arrow.mk (E i).inv := by
    simp only [f, Functor.map_comp, eqToHom_map, Arrow.arrow_mk_comp_eqToHom]
    exact (congrArg (fun H : F.obj k ⟶ V.pt => Arrow.mk (H.toFunctor.map (B i).hom))
      (V.w r)).trans (hB i)
  have hg (i : ι) : Arrow.mk ((V.ι.app l).toFunctor.map (g i)) =
      Arrow.mk (E i).hom := by
    simp only [g, Functor.map_comp, eqToHom_map, Arrow.arrow_mk_comp_eqToHom,
      Arrow.arrow_mk_eqToHom_comp]
    exact (congrArg (fun H : F.obj k ⟶ V.pt => Arrow.mk (H.toFunctor.map (C i).hom))
      (V.w r)).trans (hC i)
  have hfg (i : ι) : Arrow.mk ((V.ι.app l).toFunctor.map (f i ≫ g i)) =
      Arrow.mk ((V.ι.app l).toFunctor.map (𝟙 (B' i).left)) := by
    calc
      _ = Arrow.mk ((E i).inv ≫ (E i).hom) := by
        simpa only [Functor.map_comp, Arrow.mk_hom, Arrow.mk_right, eqToHom_refl,
          Category.id_comp] using
          arrow_comp_congr (hf i) (hg i) rfl rfl
      _ = Arrow.mk (𝟙 (Z i)) := congrArg Arrow.mk (E i).inv_hom_id
      _ = _ := by
        simpa only [Functor.map_id, Arrow.mk_left] using
          congrArg (fun z => Arrow.mk (𝟙 z)) (congrArg Arrow.left (hf i)).symm
  have hgf (i : ι) : Arrow.mk ((V.ι.app l).toFunctor.map (g i ≫ f i)) =
      Arrow.mk ((V.ι.app l).toFunctor.map (𝟙 (W.obj (T i)))) := by
    calc
      _ = Arrow.mk ((E i).hom ≫ (E i).inv) := by
        simpa only [Functor.map_comp, Arrow.mk_hom, Arrow.mk_right, eqToHom_refl,
          Category.id_comp] using
          arrow_comp_congr (hg i) (hf i) rfl rfl
      _ = Arrow.mk (𝟙 ((V.ι.app j).toFunctor.obj (D i))) :=
        congrArg Arrow.mk (E i).hom_inv_id
      _ = _ := by
        simpa only [Functor.map_id, Arrow.mk_left] using
          congrArg (fun z => Arrow.mk (𝟙 z)) (congrArg Arrow.left (hg i)).symm
  let P : ι × Bool → Arrow (F.obj l) := fun p =>
    if p.2 then Arrow.mk (g p.1 ≫ f p.1) else Arrow.mk (f p.1 ≫ g p.1)
  let Q : ι × Bool → Arrow (F.obj l) := fun p =>
    if p.2 then Arrow.mk (𝟙 (W.obj (T p.1))) else Arrow.mk (𝟙 (B' p.1).left)
  have hPQ (p : ι × Bool) :
      (Cat.arrows.mapCocone V).ι.app l (P p) =
        (Cat.arrows.mapCocone V).ι.app l (Q p) := by
    rcases p with ⟨i, b⟩
    cases b
    · exact hfg i
    · exact hgf i
  obtain ⟨m, s, hs⟩ := finite_stage_eq (F ⋙ Cat.arrows)
    (Cat.arrows.mapCocone V) harrows l P Q hPQ
  let U := (F.map s).toFunctor
  have hfs (i : ι) : U.map (f i) ≫ U.map (g i) = 𝟙 (U.obj (B' i).left) := by
    apply Arrow.mk_injective
    have h := hs (i, false)
    change Arrow.mk (U.map (f i ≫ g i)) = Arrow.mk (U.map (𝟙 (B' i).left)) at h
    simpa only [Functor.map_comp, Functor.map_id] using h
  have hgs (i : ι) : U.map (g i) ≫ U.map (f i) = 𝟙 (U.obj (W.obj (T i))) := by
    apply Arrow.mk_injective
    have h := hs (i, true)
    change Arrow.mk (U.map (g i ≫ f i)) = Arrow.mk (U.map (𝟙 (W.obj (T i)))) at h
    simpa only [Functor.map_comp, Functor.map_id] using h
  let e : ∀ i, U.obj (B' i).left ≅ U.obj (W.obj (T i)) :=
    fun i => ⟨U.map (f i), U.map (g i), hfs i, hgs i⟩
  have htarget (i : ι) : U.obj (W.obj (T i)) =
      (F.map (c ≫ r ≫ s)).toFunctor.obj (D i) := by
    simp only [Functor.map_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj, U, W, T]
  refine ⟨m, c ≫ r ≫ s, fun i => U.obj (B' i).left,
    fun i => e i ≪≫ eqToIso (htarget i), fun i => ?_⟩
  simp only [Iso.trans_hom, eqToIso.hom, Functor.map_comp, eqToHom_map,
    Arrow.arrow_mk_comp_eqToHom]
  exact (congrArg (fun H : F.obj l ⟶ V.pt => Arrow.mk (H.toFunctor.map (f i)))
    (V.w s)).trans (hf i)

end CategoryTheory
