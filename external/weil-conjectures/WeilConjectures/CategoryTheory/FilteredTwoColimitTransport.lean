/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import WeilConjectures.CategoryTheory.FilteredTwoColimit

/-!
# Transport of filtered 2-colimits along stagewise equivalences

Let `c'` be a cocone of categories on a directed system `C' i` with vertex `D`, and let
`F i : C i ⥤ C' i` be equivalences from the stages of another directed system `C i`, compatible
with the transition functors up to isomorphisms `β h : T h ⋙ F j ≅ F i ⋙ T' h`. Composing
with the `F i` gives a cocone `CategoryCocone.transport` on the `C i` with the same vertex, and it
is a filtered 2-colimit as soon as `c'` is
(`CategoryTheory.CategoryCocone.IsFilteredTwoColimit.transport`):
a functor between filtered 2-colimits defined stagewise by equivalences is an equivalence. No
compatibility of the `β h` with the composition of the transition functors is needed.
-/

@[expose] public section

namespace CategoryTheory

namespace CategoryCocone

variable {I : Type*} [Preorder I] {C C' : I → Type*} [∀ i, Category* (C i)]
  [∀ i, Category* (C' i)] {D : Type*} [Category* D] (c' : CategoryCocone C' D)
  (T : ∀ {i j : I}, i ≤ j → (C i ⥤ C j)) (F : ∀ i, C i ⥤ C' i)
  (β : ∀ {i j : I} (h : i ≤ j), T h ⋙ F j ≅ F i ⋙ c'.T h)

/-- The cocone on the `C i` obtained by composing `c'` with stagewise functors `F i`. -/
abbrev transport : CategoryCocone C D where
  T h := T h
  Φ i := F i ⋙ c'.Φ i
  iso {i j} h := NatIso.ofComponents
    (fun x ↦ (c'.Φ j).mapIso ((β h).app x) ≪≫ (c'.iso h).app ((F i).obj x))
    fun {x y} f ↦ by
      simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
      rw [← Functor.map_comp_assoc]
      have := (β h).hom.naturality f
      simp only [Functor.comp_map] at this
      rw [this, Functor.map_comp_assoc]
      exact (congrArg ((c'.Φ j).map ((β h).hom.app x) ≫ ·)
        ((c'.iso h).hom.naturality ((F i).map f))).trans (Category.assoc _ _ _).symm

variable {c' T F β}

/-- A cocone obtained by transport along stagewise equivalences from a filtered 2-colimit is a
filtered 2-colimit. -/
theorem IsFilteredTwoColimit.transport [∀ i, (F i).IsEquivalence] (hc' : c'.IsFilteredTwoColimit) :
    (c'.transport T F β).IsFilteredTwoColimit where
  essSurjObj d := by
    obtain ⟨i, x', ⟨e⟩⟩ := hc'.essSurjObj d
    exact ⟨i, (F i).objPreimage x',
      ⟨(c'.Φ i).mapIso ((F i).objObjPreimageIso x') ≪≫ e⟩⟩
  homSurj i j x y f := by
    obtain ⟨k, hi, hj, g', hg'⟩ := hc'.homSurj i j ((F i).obj x) ((F j).obj y) f
    refine ⟨k, hi, hj, (F k).preimage ((β hi).hom.app x ≫ g' ≫ (β hj).inv.app y), ?_⟩
    simp only [Functor.comp_obj, Functor.comp_map, Functor.map_preimage,
      NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app, Iso.trans_inv, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Functor.map_comp,
      Category.assoc]
    rw [hg']
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  homInj k x y g g' h := by
    obtain ⟨k', hk, h'⟩ := hc'.homInj k ((F k).obj x) ((F k).obj y) ((F k).map g) ((F k).map g') h
    refine ⟨k', hk, (F k').map_injective ?_⟩
    have e (u : x ⟶ y) : (F k').map ((T hk).map u) =
        (β hk).hom.app x ≫ (c'.T hk).map ((F k).map u) ≫ (β hk).inv.app y := by
      rw [← Functor.comp_map, ← Functor.comp_map, ← (β hk).hom.naturality_assoc,
        Iso.hom_inv_id_app, Category.comp_id]
    rw [e, e, h']

end CategoryCocone

end CategoryTheory
