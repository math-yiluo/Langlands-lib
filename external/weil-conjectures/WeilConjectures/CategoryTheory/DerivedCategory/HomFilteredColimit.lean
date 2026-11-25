/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit

/-!
# Morphisms out of an object of `D(C)` commuting with filtered colimits

Let `C` be an abelian category and `s` an object of its derived category. We say that
`Hom(s, -[n])` *commutes with filtered colimits* of objects of `C`
(`DerivedCategory.HomCommutesWithFilteredColimits`) if for every filtered colimit
`B = colim Bᵢ` in `C` and every `n`, the canonical map `colim Hom(s, Bᵢ[n]) ⟶ Hom(s, B[n])` is
bijective. This is blueprint `lemma-continuity-ext-out-constructible-complex--1` for targets in
degree `0`.

* The class of such `s` contains zero, is closed under isomorphisms, shifts and extensions
  (blueprint `lemma-continuity-ext-out-constructible-complex--1`, five lemma).
* For `s` bounded above, the comparison is then bijective for every filtered diagram `Yᵢ` in
  `D(C)` of uniformly bounded below objects with a cocone `Y` inducing colimits on cohomology
  (`DerivedCategory.HomCommutesWithFilteredColimits.diagram`), by induction on the amplitude
  along the truncation triangles.
* The class is transported along adjunctions `F ⊣ G` whose right adjoint `G` is left
  `t`-exact up to a shift and commutes with filtered colimits on cohomology
  (`DerivedCategory.HomCommutesWithFilteredColimits.of_adjunction`), and along adjunctions of
  exact functors whose right adjoint preserves filtered colimits
  (`DerivedCategory.HomCommutesWithFilteredColimits.mapDerivedCategory`).

The proofs go through the general notion `CategoryTheory.Limits.Cocone.IsCoyonedaColimit s c`
(every morphism `s ⟶ c.pt` factors through the diagram, and a morphism `s ⟶ X i` vanishing in
`c.pt` vanishes in some `X j`), for which we prove the five lemmas in a pretriangulated
category, in the source (`Cocone.IsCoyonedaColimit.of_distTriang_source`) and in the target
(`Cocone.IsCoyonedaColimit.of_distTriang_target`), and the transport along adjunctions
(`Cocone.IsCoyonedaColimit.adjunction_iff`).
-/

@[expose] public section

universe w

open CategoryTheory Category Limits Pretriangulated Preadditive

namespace CategoryTheory.Pretriangulated.Triangle

section

variable {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]

/-- The morphism `T.obj₃⟦-1⟧ ⟶ T.obj₁` of a triangle `T`: the first morphism of `T.invRotate`
(which is the opposite of the shift of `T.mor₃`), with a convenient type. -/
noncomputable def invRotateMor₁ (T : Triangle D) : T.obj₃⟦(-1 : ℤ)⟧ ⟶ T.obj₁ :=
  T.invRotate.mor₁

/-- Naturality of the morphism `T.obj₃⟦-1⟧ ⟶ T.obj₁` of the inverse rotation. -/
@[reassoc]
lemma invRotateMor₁_naturality {T T' : Triangle D} (φ : T ⟶ T') :
    T.invRotateMor₁ ≫ φ.hom₁ = φ.hom₃⟦(-1 : ℤ)⟧' ≫ T'.invRotateMor₁ :=
  ((Pretriangulated.invRotate D).map φ).comm₁

end

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- The morphism `T.obj₃⟦-1⟧ ⟶ T.obj₁` of a distinguished triangle `T` composes to zero with
`T.mor₁`. -/
lemma invRotateMor₁_comp_mor₁ (T : Triangle D) (hT : T ∈ distTriang D) :
    T.invRotateMor₁ ≫ T.mor₁ = 0 :=
  comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hT)

/-- Exactness of `Hom(T.obj₂, Z) ⟶ Hom(T.obj₁, Z) ⟶ Hom(T.obj₃⟦-1⟧, Z)` for a distinguished
triangle `T`. -/
lemma yoneda_exact₁ (T : Triangle D) (hT : T ∈ distTriang D) {Z : D} (f : T.obj₁ ⟶ Z)
    (hf : T.invRotateMor₁ ≫ f = 0) : ∃ g : T.obj₂ ⟶ Z, f = T.mor₁ ≫ g :=
  Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) f hf

/-- Exactness of `Hom(Z, T.obj₃⟦-1⟧) ⟶ Hom(Z, T.obj₁) ⟶ Hom(Z, T.obj₂)` for a distinguished
triangle `T`. -/
lemma coyoneda_exact₁' (T : Triangle D) (hT : T ∈ distTriang D) {Z : D} (f : Z ⟶ T.obj₁)
    (hf : f ≫ T.mor₁ = 0) : ∃ g : Z ⟶ T.obj₃⟦(-1 : ℤ)⟧, f = g ≫ T.invRotateMor₁ :=
  Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT) f hf

end CategoryTheory.Pretriangulated.Triangle

namespace CategoryTheory.Limits.Cocone

section Preadditive

variable {D : Type*} [Category* D] [Preadditive D]

/-- A cocone `c` over a diagram `X : I ⥤ D` is a *colimit for `Hom(s, -)`* if every morphism
`s ⟶ c.pt` factors through some `X i`, and every morphism `s ⟶ X i` which vanishes in `c.pt`
vanishes in some `X j`. For `I` filtered, this says that `Hom(s, -)` sends `c` to a colimit. -/
def IsCoyonedaColimit (s : D) {I : Type*} [Category* I] {X : I ⥤ D} (c : Cocone X) : Prop :=
  (∀ f : s ⟶ c.pt, ∃ (i : I) (g : s ⟶ X.obj i), f = g ≫ c.ι.app i) ∧
    ∀ (i : I) (g : s ⟶ X.obj i), g ≫ c.ι.app i = 0 → ∃ (j : I) (t : i ⟶ j), g ≫ X.map t = 0

namespace IsCoyonedaColimit

variable {I : Type*} [Category* I]

/-- A zero object `s` satisfies `IsCoyonedaColimit` for every cocone over a nonempty index
category. -/
lemma of_isZero [Nonempty I] {s : D} (hs : IsZero s) {X : I ⥤ D} (c : Cocone X) :
    IsCoyonedaColimit s c := by
  refine ⟨fun f ↦ ⟨Classical.arbitrary I, 0, hs.eq_of_src _ _⟩, fun i g _ ↦ ⟨i, 𝟙 i, ?_⟩⟩
  exact hs.eq_of_src _ _

/-- `IsCoyonedaColimit` is invariant under isomorphisms of the source. -/
lemma of_iso {s s' : D} (e : s ≅ s') {X : I ⥤ D} {c : Cocone X}
    (hs : IsCoyonedaColimit s c) : IsCoyonedaColimit s' c := by
  refine ⟨fun f ↦ ?_, fun i g hg ↦ ?_⟩
  · obtain ⟨i, g, hg⟩ := hs.1 (e.hom ≫ f)
    exact ⟨i, e.inv ≫ g, by rw [assoc, ← hg, Iso.inv_hom_id_assoc]⟩
  · obtain ⟨j, t, ht⟩ := hs.2 i (e.hom ≫ g) (by rw [assoc, hg, comp_zero])
    refine ⟨j, t, ?_⟩
    rw [← cancel_epi e.hom, comp_zero, ← ht, assoc]

/-- `IsCoyonedaColimit` is transported along a morphism of diagrams `α : X' ⟶ X` compatible
with the cocones, such that composition with `α` is surjective on morphisms out of `s` and
composition with the map of cocone points is bijective. -/
lemma of_hom {s : D} {X X' : I ⥤ D} {c : Cocone X} {c' : Cocone X'} (α : X' ⟶ X)
    (αpt : c'.pt ⟶ c.pt) (hα : ∀ i, c'.ι.app i ≫ αpt = α.app i ≫ c.ι.app i)
    (hsurj : ∀ i, Function.Surjective fun g : s ⟶ X'.obj i ↦ g ≫ α.app i)
    (hpt : Function.Bijective fun f : s ⟶ c'.pt ↦ f ≫ αpt)
    (h : IsCoyonedaColimit s c') : IsCoyonedaColimit s c := by
  refine ⟨fun f ↦ ?_, fun i g hg ↦ ?_⟩
  · obtain ⟨f', rfl⟩ := hpt.2 f
    obtain ⟨i, g, rfl⟩ := h.1 f'
    exact ⟨i, g ≫ α.app i, by simp only [assoc, hα]⟩
  · obtain ⟨g', rfl⟩ := hsurj i g
    obtain ⟨j, t, ht⟩ := h.2 i g' (hpt.1 (by simpa only [assoc, hα, zero_comp] using hg))
    exact ⟨j, t, by rw [assoc, ← α.naturality, ← assoc, ht, zero_comp]⟩

/-- `IsCoyonedaColimit` is transported along an isomorphism of diagrams compatible with an
isomorphism of the cocone points. -/
lemma of_natIso {s : D} {X X' : I ⥤ D} {c : Cocone X} {c' : Cocone X'} (α : X' ≅ X)
    (αpt : c'.pt ≅ c.pt) (hα : ∀ i, c'.ι.app i ≫ αpt.hom = α.hom.app i ≫ c.ι.app i)
    (h : IsCoyonedaColimit s c') : IsCoyonedaColimit s c :=
  of_hom α.hom αpt.hom hα (fun i g ↦ ⟨g ≫ α.inv.app i, by simp⟩)
    ⟨fun f₁ f₂ hf ↦ by simpa using hf =≫ αpt.inv, fun f ↦ ⟨f ≫ αpt.inv, by simp⟩⟩ h

/-- `IsCoyonedaColimit` for the image of a cocone under a functor only depends on the functor
up to isomorphism. -/
lemma mapCocone_of_iso {D' : Type*} [Category* D'] {s : D} {X : I ⥤ D'} (c : Cocone X)
    {G G' : D' ⥤ D} (φ : G ≅ G') (h : IsCoyonedaColimit s (G.mapCocone c)) :
    IsCoyonedaColimit s (G'.mapCocone c) :=
  of_natIso (Functor.isoWhiskerLeft X φ) (φ.app c.pt) (fun i ↦ φ.hom.naturality (c.ι.app i)) h

/-- `IsCoyonedaColimit` along an adjunction: morphisms `L s ⟶ -` are morphisms `s ⟶ R -`. -/
lemma adjunction_iff {D' : Type*} [Category* D'] [Preadditive D'] {L : D ⥤ D'} {R : D' ⥤ D}
    (adj : L ⊣ R) [L.PreservesZeroMorphisms] [R.PreservesZeroMorphisms] (s : D)
    {X : I ⥤ D'} (c : Cocone X) :
    IsCoyonedaColimit (L.obj s) c ↔ IsCoyonedaColimit s (R.mapCocone c) := by
  have e₀ {Y : D'} (f : L.obj s ⟶ Y) : adj.homEquiv _ _ f = 0 ↔ f = 0 := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← (adj.homEquiv _ _).symm_apply_apply f, h, Adjunction.homEquiv_counit,
        Functor.map_zero, zero_comp]
    · rw [h, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  refine ⟨fun h ↦ ⟨fun f ↦ ?_, fun i g hg ↦ ?_⟩, fun h ↦ ⟨fun f ↦ ?_, fun i g hg ↦ ?_⟩⟩
  · obtain ⟨i, g, hg⟩ := h.1 ((adj.homEquiv _ _).symm f)
    refine ⟨i, adj.homEquiv _ _ g, ?_⟩
    rw [Functor.mapCocone_ι_app, ← Adjunction.homEquiv_naturality_right, ← hg,
      Equiv.apply_symm_apply]
  · obtain ⟨j, t, ht⟩ := h.2 i ((adj.homEquiv _ _).symm g) (by
      rw [← e₀, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
      exact hg)
    refine ⟨j, t, ?_⟩
    rw [← e₀, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] at ht
    exact ht
  · obtain ⟨i, g, hg⟩ := h.1 (adj.homEquiv _ _ f)
    refine ⟨i, (adj.homEquiv _ _).symm g, ?_⟩
    rw [← Adjunction.homEquiv_naturality_right_symm, ← Functor.mapCocone_ι_app, ← hg]
    exact ((adj.homEquiv _ _).symm_apply_apply f).symm
  · obtain ⟨j, t, ht⟩ := h.2 i (adj.homEquiv _ _ g) (by
      rw [Functor.mapCocone_ι_app, ← Adjunction.homEquiv_naturality_right, e₀]
      exact hg)
    refine ⟨j, t, ?_⟩
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_right, e₀] at ht
    exact ht

end IsCoyonedaColimit

end Preadditive

section Pretriangulated

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace IsCoyonedaColimit

variable {I : Type*} [Category* I] [IsFiltered I]

/-- Five lemma in the source: for a distinguished triangle `T`, if `T.obj₁`, `T.obj₃`,
`T.obj₁⟦1⟧` and `T.obj₃⟦-1⟧` satisfy `IsCoyonedaColimit` for a cocone over a filtered
category, so does `T.obj₂`. -/
lemma of_distTriang_source {X : I ⥤ D} {c : Cocone X} (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : IsCoyonedaColimit T.obj₁ c) (h₃ : IsCoyonedaColimit T.obj₃ c)
    (h₁' : IsCoyonedaColimit (T.obj₁⟦(1 : ℤ)⟧) c)
    (h₃' : IsCoyonedaColimit (T.obj₃⟦(-1 : ℤ)⟧) c) :
    IsCoyonedaColimit T.obj₂ c := by
  have hu := T.invRotateMor₁_comp_mor₁ hT
  refine ⟨fun f ↦ ?_, fun i g hg ↦ ?_⟩
  · obtain ⟨i, a, ha⟩ := h₁.1 (T.mor₁ ≫ f)
    obtain ⟨j, t, ht⟩ := h₃'.2 i (T.invRotateMor₁ ≫ a) (by
      rw [assoc, ← ha, ← assoc, hu, zero_comp])
    obtain ⟨b, hb⟩ := T.yoneda_exact₁ hT (a ≫ X.map t) ((assoc _ _ _).symm.trans ht)
    obtain ⟨d, hd⟩ := Triangle.yoneda_exact₂ _ hT (f - (b ≫ c.ι.app j : T.obj₂ ⟶ c.pt)) (by
      rw [comp_sub, ← assoc, ← hb, assoc, c.w, ← ha, sub_self])
    obtain ⟨k, d', rfl⟩ := h₃.1 d
    refine ⟨IsFiltered.max j k, b ≫ X.map (IsFiltered.leftToMax j k) +
      T.mor₂ ≫ d' ≫ X.map (IsFiltered.rightToMax j k), ?_⟩
    rw [add_comp, assoc, assoc, assoc, c.w, c.w, ← hd]
    abel
  · obtain ⟨j, t, ht⟩ := h₁.2 i (T.mor₁ ≫ g) (by rw [assoc, hg, comp_zero])
    obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ _ hT (g ≫ X.map t) (by rw [← assoc]; exact ht)
    obtain ⟨e, he⟩ := Triangle.yoneda_exact₃ _ hT (h ≫ c.ι.app j) (by
      rw [← assoc, ← hh, assoc, c.w, hg])
    obtain ⟨k, e', rfl⟩ := h₁'.1 e
    obtain ⟨p, u, hu⟩ := h₃.2 (IsFiltered.max j k) (h ≫ X.map (IsFiltered.leftToMax j k) -
      T.mor₃ ≫ e' ≫ X.map (IsFiltered.rightToMax j k)) (by
      rw [sub_comp, assoc, assoc, assoc, c.w, c.w, he, sub_self])
    refine ⟨p, t ≫ IsFiltered.leftToMax j k ≫ u, ?_⟩
    simp only [sub_comp, sub_eq_zero, assoc, ← X.map_comp] at hu
    rw [X.map_comp, ← assoc, hh, assoc, hu,
      comp_distTriang_mor_zero₂₃_assoc _ hT, zero_comp]

/-- Auxiliary statement for `IsCoyonedaColimit.of_distTriang_target`, with the cocone given by
an explicit family of morphisms of triangles `ι i : T.obj i ⟶ P`. -/
lemma of_distTriang_target_aux {s : D} {T : I ⥤ Triangle D} {P : Triangle D}
    (ι : ∀ i, T.obj i ⟶ P) (w : ∀ {i j : I} (t : i ⟶ j), T.map t ≫ ι j = ι i)
    (hT : ∀ i, T.obj i ∈ distTriang D) (hc : P ∈ distTriang D)
    (h₁ : (∀ f : s ⟶ P.obj₁, ∃ (i : I) (g : s ⟶ (T.obj i).obj₁), f = g ≫ (ι i).hom₁) ∧
      ∀ (i : I) (g : s ⟶ (T.obj i).obj₁), g ≫ (ι i).hom₁ = 0 →
        ∃ (j : I) (t : i ⟶ j), g ≫ (T.map t).hom₁ = 0)
    (h₃ : (∀ f : s ⟶ P.obj₃, ∃ (i : I) (g : s ⟶ (T.obj i).obj₃), f = g ≫ (ι i).hom₃) ∧
      ∀ (i : I) (g : s ⟶ (T.obj i).obj₃), g ≫ (ι i).hom₃ = 0 →
        ∃ (j : I) (t : i ⟶ j), g ≫ (T.map t).hom₃ = 0)
    (h₁' : ∀ (i : I) (g : s ⟶ (T.obj i).obj₁⟦(1 : ℤ)⟧), g ≫ (ι i).hom₁⟦(1 : ℤ)⟧' = 0 →
      ∃ (j : I) (t : i ⟶ j), g ≫ (T.map t).hom₁⟦(1 : ℤ)⟧' = 0)
    (h₃' : ∀ f : s ⟶ P.obj₃⟦(-1 : ℤ)⟧, ∃ (i : I) (g : s ⟶ (T.obj i).obj₃⟦(-1 : ℤ)⟧),
      f = g ≫ (ι i).hom₃⟦(-1 : ℤ)⟧') :
    (∀ f : s ⟶ P.obj₂, ∃ (i : I) (g : s ⟶ (T.obj i).obj₂), f = g ≫ (ι i).hom₂) ∧
      ∀ (i : I) (g : s ⟶ (T.obj i).obj₂), g ≫ (ι i).hom₂ = 0 →
        ∃ (j : I) (t : i ⟶ j), g ≫ (T.map t).hom₂ = 0 := by
  have w₁ {i j : I} (t : i ⟶ j) : (T.map t).hom₁ ≫ (ι j).hom₁ = (ι i).hom₁ := by
    rw [← comp_hom₁, w]
  have w₂ {i j : I} (t : i ⟶ j) : (T.map t).hom₂ ≫ (ι j).hom₂ = (ι i).hom₂ := by
    rw [← comp_hom₂, w]
  have w₃ {i j : I} (t : i ⟶ j) : (T.map t).hom₃ ≫ (ι j).hom₃ = (ι i).hom₃ := by
    rw [← comp_hom₃, w]
  refine ⟨fun f ↦ ?_, fun i g hg ↦ ?_⟩
  · obtain ⟨i, g, hg⟩ := h₃.1 (f ≫ P.mor₂)
    obtain ⟨j, t, ht⟩ := h₁' i (g ≫ (T.obj i).mor₃) (by
      rw [assoc, TriangleMorphism.comm₃, ← assoc, ← hg, assoc, comp_distTriang_mor_zero₂₃ _ hc,
        comp_zero])
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃ _ (hT j) (g ≫ (T.map t).hom₃) (by
      rw [assoc, ← TriangleMorphism.comm₃, ← assoc, ht])
    obtain ⟨d, hd⟩ := Triangle.coyoneda_exact₂ _ hc (f - b ≫ (ι j).hom₂) (by
      rw [sub_comp, hg, assoc, ← TriangleMorphism.comm₂, ← assoc, ← hb, assoc, w₃, sub_self])
    obtain ⟨k, d', rfl⟩ := h₁.1 d
    refine ⟨IsFiltered.max j k, b ≫ (T.map (IsFiltered.leftToMax j k)).hom₂ +
      d' ≫ (T.map (IsFiltered.rightToMax j k)).hom₁ ≫ (T.obj (IsFiltered.max j k)).mor₁, ?_⟩
    rw [add_comp, assoc, w₂, assoc, assoc, TriangleMorphism.comm₁, ← assoc (T.map _).hom₁, w₁,
      ← assoc, ← hd]
    abel
  · obtain ⟨j, t, ht⟩ := h₃.2 i (g ≫ (T.obj i).mor₂) (by
      rw [assoc, TriangleMorphism.comm₂, ← assoc, hg, zero_comp])
    obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ _ (hT j) (g ≫ (T.map t).hom₂) (by
      rw [assoc, ← TriangleMorphism.comm₂, ← assoc, ht])
    obtain ⟨e, he⟩ := Triangle.coyoneda_exact₁' _ hc (h ≫ (ι j).hom₁) (by
      rw [assoc, ← TriangleMorphism.comm₁, ← assoc, ← hh, assoc, w₂, hg])
    obtain ⟨k, e', rfl⟩ := h₃' e
    obtain ⟨p, v, hv⟩ := h₁.2 (IsFiltered.max j k)
      (h ≫ (T.map (IsFiltered.leftToMax j k)).hom₁ -
        e' ≫ (T.map (IsFiltered.rightToMax j k)).hom₃⟦(-1 : ℤ)⟧' ≫
          (T.obj (IsFiltered.max j k)).invRotateMor₁) (by
      rw [sub_comp, assoc, w₁, he, sub_eq_zero]
      simp only [assoc, Triangle.invRotateMor₁_naturality, ← Functor.map_comp_assoc, w₃])
    refine ⟨p, t ≫ IsFiltered.leftToMax j k ≫ v, ?_⟩
    simp only [sub_comp, sub_eq_zero, assoc] at hv
    simp only [Functor.map_comp, comp_hom₂]
    rw [reassoc_of% hh, TriangleMorphism.comm₁_assoc, TriangleMorphism.comm₁, reassoc_of% hv,
      Triangle.invRotateMor₁_naturality_assoc, Triangle.invRotateMor₁_comp_mor₁ _ (hT p)]
    simp

/-- Five lemma in the target: let `T` be a diagram of distinguished triangles over a filtered
category with a cocone `c` whose point is distinguished. If `s` satisfies `IsCoyonedaColimit`
for the cocones of first and third objects, and for the cocones of shifted first objects
`T.obj₁⟦1⟧` and shifted third objects `T.obj₃⟦-1⟧`, then so it does for the second objects. -/
lemma of_distTriang_target {s : D} {T : I ⥤ Triangle D} (c : Cocone T)
    (hT : ∀ i, T.obj i ∈ distTriang D) (hc : c.pt ∈ distTriang D)
    (h₁ : IsCoyonedaColimit s (Triangle.π₁.mapCocone c))
    (h₃ : IsCoyonedaColimit s (Triangle.π₃.mapCocone c))
    (h₁' : IsCoyonedaColimit s ((Triangle.π₁ ⋙ shiftFunctor D (1 : ℤ)).mapCocone c))
    (h₃' : IsCoyonedaColimit s ((Triangle.π₃ ⋙ shiftFunctor D (-1 : ℤ)).mapCocone c)) :
    IsCoyonedaColimit s (Triangle.π₂.mapCocone c) :=
  of_distTriang_target_aux (fun i ↦ c.ι.app i) (fun t ↦ c.w t) hT hc h₁ h₃ h₁'.2 h₃'.1

end IsCoyonedaColimit

end Pretriangulated

end CategoryTheory.Limits.Cocone

namespace DerivedCategory

open TStructure (t)
open Cocone

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
/-- Objects of `D(C)` concentrated in degree `m` are naturally isomorphic to their `m`-th

homology object placed in degree `m`. -/
lemma nonempty_ι_iso_homologyFunctor_singleFunctor (m : ℤ) :
    let P : ObjectProperty (DerivedCategory C) := t.le m ⊓ t.ge m
    Nonempty (P.ι ≅ P.ι ⋙ homologyFunctor C m ⋙ singleFunctor C m) := by
  intro P
  let Φ : C ⥤ P.FullSubcategory := P.lift (singleFunctor C m)
    fun X ↦ ⟨t.le_of_isLE _ m, t.ge_of_isGE _ m⟩
  have : Φ.EssSurj := ⟨fun Y ↦ by
    have : Y.obj.IsLE m := ⟨Y.property.1⟩
    have : Y.obj.IsGE m := ⟨Y.property.2⟩
    obtain ⟨M, ⟨e⟩⟩ := Y.obj.exists_iso_singleFunctor_obj_of_isGE_of_isLE m
    exact ⟨M, ⟨P.fullyFaithfulι.preimageIso e.symm⟩⟩⟩
  have : Φ.IsEquivalence := {}
  let E := Φ.asEquivalence
  -- `E.inverse ≅ P.ι ⋙ homologyFunctor C m`
  let e₁ : E.inverse ≅ P.ι ⋙ homologyFunctor C m :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft E.inverse (singleFunctorCompHomologyFunctorIso C m).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight E.counitIso P.ι ≪≫ P.ι.leftUnitor)
        (homologyFunctor C m)
  exact ⟨(Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm P.ι ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerRight e₁ (singleFunctor C m) ≪≫
    Functor.associator _ _ _⟩

section Truncation

variable {I : Type*} [Category* I] {Y : I ⥤ DerivedCategory C} {c : Cocone Y}

/-- If a cocone induces colimits on all homology objects, so does its truncation `τ_{< k}`. -/
lemma isColimit_homologyFunctor_mapCocone_truncLT
    (hH : ∀ n : ℤ, Nonempty (IsColimit ((homologyFunctor C n).mapCocone c))) (k n : ℤ) :
    Nonempty (IsColimit ((homologyFunctor C n).mapCocone ((t.truncLT k).mapCocone c))) := by
  by_cases hn : n < k
  · have (X : DerivedCategory C) :
        IsIso ((Functor.whiskerRight (t.truncLTι k) (homologyFunctor C n)).app X) :=
      isIso_homologyMap_mor₁ _ (t.triangleLTGE_distinguished k X) (n - 1) n (by lia)
        (isZero_of_isGE _ k _ (by lia)) (isZero_of_isGE _ k _ (by lia))
    have : IsIso (Functor.whiskerRight (t.truncLTι k) (homologyFunctor C n)) :=
      NatIso.isIso_of_isIso_app _
    obtain ⟨h⟩ := hH n
    exact ⟨IsColimit.mapCoconeEquiv (c := c) ((homologyFunctor C n).leftUnitor.symm ≪≫
      (asIso (Functor.whiskerRight (t.truncLTι k) (homologyFunctor C n))).symm) h⟩
  · exact ⟨IsColimit.ofIsZero _ (Functor.isZero _ fun i ↦
      isZero_of_isLE ((t.truncLT k).obj (Y.obj i)) (k - 1) n (by lia))
      (isZero_of_isLE ((t.truncLT k).obj c.pt) (k - 1) n (by lia))⟩

/-- If a cocone induces colimits on all homology objects, so does its truncation `τ_{≥ k}`. -/
lemma isColimit_homologyFunctor_mapCocone_truncGE
    (hH : ∀ n : ℤ, Nonempty (IsColimit ((homologyFunctor C n).mapCocone c))) (k n : ℤ) :
    Nonempty (IsColimit ((homologyFunctor C n).mapCocone ((t.truncGE k).mapCocone c))) := by
  by_cases hn : k ≤ n
  · have (X : DerivedCategory C) :
        IsIso ((Functor.whiskerRight (t.truncGEπ k) (homologyFunctor C n)).app X) :=
      isIso_homologyMap_mor₂ _ (t.triangleLTGE_distinguished k X) n (n + 1) rfl
        (isZero_of_isLE _ (k - 1) _ (by lia)) (isZero_of_isLE _ (k - 1) _ (by lia))
    have : IsIso (Functor.whiskerRight (t.truncGEπ k) (homologyFunctor C n)) :=
      NatIso.isIso_of_isIso_app _
    obtain ⟨h⟩ := hH n
    exact ⟨IsColimit.mapCoconeEquiv (c := c) ((homologyFunctor C n).leftUnitor.symm ≪≫
      asIso (Functor.whiskerRight (t.truncGEπ k) (homologyFunctor C n))) h⟩
  · exact ⟨IsColimit.ofIsZero _ (Functor.isZero _ fun i ↦
      isZero_of_isGE ((t.truncGE k).obj (Y.obj i)) k n (by lia))
      (isZero_of_isGE ((t.truncGE k).obj c.pt) k n (by lia))⟩

end Truncation

/-- Blueprint `lemma-continuity-ext-out-constructible-complex--1` for targets in degree `0`: for
every filtered colimit `B = colim Bᵢ` of objects of `C` (indexed by a category in `Type w`) and
every `n`, the map `colim Hom(s, Bᵢ[n]) ⟶ Hom(s, B[n])` is surjective (every morphism factors
through some `Bᵢ[n]`) and injective (a morphism to `Bᵢ[n]` which vanishes in `B[n]` vanishes in some
`Bⱼ[n]`). -/
def HomCommutesWithFilteredColimits (s : DerivedCategory C) : Prop :=
  ∀ (I : Type w) [SmallCategory I] [IsFiltered I] (F : I ⥤ C) (c : Cocone F)
    (_ : IsColimit c) (n : ℤ),
    (∀ f : s ⟶ (singleFunctor C n).obj c.pt, ∃ (i : I) (g : s ⟶ (singleFunctor C n).obj (F.obj i)),
      f = g ≫ (singleFunctor C n).map (c.ι.app i)) ∧
    (∀ (i : I) (g : s ⟶ (singleFunctor C n).obj (F.obj i)),
      g ≫ (singleFunctor C n).map (c.ι.app i) = 0 →
        ∃ (j : I) (t : i ⟶ j), g ≫ (singleFunctor C n).map (F.map t) = 0)

namespace HomCommutesWithFilteredColimits

/-- Surjectivity is the factorization property `HomFactorsThroughFilteredColimits`. -/
lemma homFactorsThroughFilteredColimits {s : DerivedCategory C}
    (hs : HomCommutesWithFilteredColimits.{w} s) : HomFactorsThroughFilteredColimits.{w} s :=
  fun I _ _ F c hc n f ↦ (hs I F c hc n).1 f


/-- Reformulation of `HomCommutesWithFilteredColimits` with `Cocone.IsCoyonedaColimit`. -/
lemma iff (s : DerivedCategory C) :
    HomCommutesWithFilteredColimits.{w} s ↔ ∀ (I : Type w) [SmallCategory I] [IsFiltered I]
      (F : I ⥤ C) (c : Cocone F) (_ : IsColimit c) (n : ℤ),
      ((singleFunctor C n).mapCocone c).IsCoyonedaColimit s :=
  Iff.rfl

lemma of_isZero {s : DerivedCategory C} (hs : IsZero s) :
    HomCommutesWithFilteredColimits.{w} s :=
  fun I _ _ _ c _ n ↦ have : Nonempty I := IsFiltered.nonempty
    IsCoyonedaColimit.of_isZero hs ((singleFunctor C n).mapCocone c)

lemma of_iso {s s' : DerivedCategory C} (e : s ≅ s')
    (hs : HomCommutesWithFilteredColimits.{w} s) : HomCommutesWithFilteredColimits.{w} s' :=
  fun I _ _ F c hc n ↦
    IsCoyonedaColimit.of_iso (c := (singleFunctor C n).mapCocone c) e (hs I F c hc n)

lemma shift {s : DerivedCategory C} (hs : HomCommutesWithFilteredColimits.{w} s) (a : ℤ) :
    HomCommutesWithFilteredColimits.{w} ((shiftFunctor (DerivedCategory C) a).obj s) :=
  fun I _ _ F c hc n ↦ (IsCoyonedaColimit.adjunction_iff
    (shiftEquiv' (DerivedCategory C) a (-a) (add_neg_cancel a)).toAdjunction s
    ((singleFunctor C n).mapCocone c)).2
      (IsCoyonedaColimit.mapCocone_of_iso c
        ((singleFunctors C).shiftIso (-a) (n + a) n (by lia)).symm (hs I F c hc (n + a)))

/-- Blueprint `lemma-continuity-ext-out-constructible-complex--1`: the class is closed under
extensions (five lemma on the long exact `Hom` sequences, filtered colimits of abelian groups
being exact). -/
lemma ext₂ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₁ : HomCommutesWithFilteredColimits.{w} T.obj₁)
    (h₃ : HomCommutesWithFilteredColimits.{w} T.obj₃) :
    HomCommutesWithFilteredColimits.{w} T.obj₂ :=
  fun I _ _ F c hc n ↦ IsCoyonedaColimit.of_distTriang_source
    (c := (singleFunctor C n).mapCocone c) T hT (h₁ I F c hc n) (h₃ I F c hc n)
    (h₁.shift 1 I F c hc n) (h₃.shift (-1) I F c hc n)

lemma ext₃ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₁ : HomCommutesWithFilteredColimits.{w} T.obj₁)
    (h₂ : HomCommutesWithFilteredColimits.{w} T.obj₂) :
    HomCommutesWithFilteredColimits.{w} T.obj₃ :=
  ext₂ T.rotate (rot_of_distTriang _ hT) h₂ (h₁.shift 1)

lemma ext₁ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (h₂ : HomCommutesWithFilteredColimits.{w} T.obj₂)
    (h₃ : HomCommutesWithFilteredColimits.{w} T.obj₃) :
    HomCommutesWithFilteredColimits.{w} T.obj₁ :=
  ext₂ T.invRotate (inv_rot_of_distTriang _ hT) (h₃.shift (-1)) h₂

/-- The case of a diagram of objects concentrated in a single degree `m`, with a cocone inducing
a colimit on `H^m`. -/
lemma isCoyonedaColimit_of_isGE_of_isLE_self {s : DerivedCategory C}
    (hs : HomCommutesWithFilteredColimits.{w} s) {I : Type w} [SmallCategory I] [IsFiltered I]
    {Y : I ⥤ DerivedCategory C} (c : Cocone Y) (m : ℤ) (hY : ∀ i, (Y.obj i).IsGE m)
    (hY' : ∀ i, (Y.obj i).IsLE m) (hc : c.pt.IsGE m) (hc' : c.pt.IsLE m)
    (hH : IsColimit ((homologyFunctor C m).mapCocone c)) : c.IsCoyonedaColimit s := by
  obtain ⟨η⟩ := nonempty_ι_iso_homologyFunctor_singleFunctor (C := C) m
  let P : ObjectProperty (DerivedCategory C) := t.le m ⊓ t.ge m
  let Y' (i : I) : P.FullSubcategory := ⟨Y.obj i, (hY' i).le, (hY i).ge⟩
  let c' : P.FullSubcategory := ⟨c.pt, hc'.le, hc.ge⟩
  refine IsCoyonedaColimit.of_natIso (c' := (singleFunctor C m).mapCocone
      ((homologyFunctor C m).mapCocone c))
    (NatIso.ofComponents (fun i ↦ (η.app (Y' i)).symm) fun {i j} f ↦ ?_) (η.app c').symm
    (fun i ↦ ?_) (hs I _ _ hH m)
  · simpa [Y'] using η.inv.naturality (P.homMk (Y.map f) : Y' i ⟶ Y' j)
  · simpa [Y', c'] using η.inv.naturality (P.homMk (c.ι.app i) : Y' i ⟶ c')



/-- The bounded case of `HomCommutesWithFilteredColimits.diagram`: diagrams of objects
concentrated in degrees `[a, a + d]`, by induction on `d` along the truncation triangles. -/
lemma isCoyonedaColimit_of_isGE_of_isLE {I : Type w} [SmallCategory I] [IsFiltered I] (d : ℕ) :
    ∀ (s : DerivedCategory C) (_ : HomCommutesWithFilteredColimits.{w} s) (a : ℤ)
      {Y : I ⥤ DerivedCategory C} (c : Cocone Y) (_ : ∀ i, (Y.obj i).IsGE a)
      (_ : ∀ i, (Y.obj i).IsLE (a + d)) (_ : c.pt.IsGE a) (_ : c.pt.IsLE (a + d))
      (_ : ∀ n : ℤ, Nonempty (IsColimit ((homologyFunctor C n).mapCocone c))),
      c.IsCoyonedaColimit s := by
  induction d with
  | zero =>
    intro s hs a Y c hY hY' hc hc' hH
    exact isCoyonedaColimit_of_isGE_of_isLE_self hs c a hY (fun i ↦ by simpa using hY' i) hc
      (by simpa using hc') (hH a).some
  | succ d ih =>
    intro s hs a Y c hY hY' hc hc' hH
    let b : ℤ := a + (d + 1 : ℕ)
    have hle (X : DerivedCategory C) : ((t.truncLT b).obj X).IsLE (a + d) :=
      t.isLE_of_le _ (b - 1) _ (by push_cast [b]; lia)
    have hge (X : DerivedCategory C) [X.IsLE b] : ((t.truncGE b).obj X).IsLE b := inferInstance
    let cT := (t.triangleLTGE b).mapCocone c
    -- the cocone of the truncations `τ_{< b}`, by induction
    have h₁ (s' : DerivedCategory C) (hs' : HomCommutesWithFilteredColimits.{w} s') :
        (Triangle.π₁.mapCocone cT).IsCoyonedaColimit s' :=
      ih s' hs' a ((t.truncLT b).mapCocone c)
        (fun i ↦ by have := hY i; exact (inferInstance : ((t.truncLT b).obj (Y.obj i)).IsGE a))
        (fun i ↦ hle _) (by have := hc; exact (inferInstance : ((t.truncLT b).obj c.pt).IsGE a))
        (hle _)
        (isColimit_homologyFunctor_mapCocone_truncLT hH b)
    -- the cocone of the truncations `τ_{≥ b}`, concentrated in degree `b`
    have h₃ (s' : DerivedCategory C) (hs' : HomCommutesWithFilteredColimits.{w} s') :
        (Triangle.π₃.mapCocone cT).IsCoyonedaColimit s' :=
      isCoyonedaColimit_of_isGE_of_isLE_self hs' ((t.truncGE b).mapCocone c) b
        (fun i ↦ (inferInstance : ((t.truncGE b).obj (Y.obj i)).IsGE b))
        (fun i ↦ by have := hY' i; exact hge _) (inferInstance : ((t.truncGE b).obj c.pt).IsGE b)
        (by have := hc'; exact hge _) (isColimit_homologyFunctor_mapCocone_truncGE hH b b).some
    exact IsCoyonedaColimit.of_distTriang_target cT (fun i ↦ t.triangleLTGE_distinguished b _)
      (t.triangleLTGE_distinguished b _) (h₁ s hs) (h₃ s hs)
      ((IsCoyonedaColimit.adjunction_iff
        (shiftEquiv' (DerivedCategory C) (-1 : ℤ) 1 (by norm_num)).toAdjunction s _).1
          (h₁ _ (hs.shift (-1))))
      ((IsCoyonedaColimit.adjunction_iff (shiftEquiv (DerivedCategory C) (1 : ℤ)).toAdjunction
        s _).1 (h₃ _ (hs.shift 1)))

/-- The bounded below case of `HomCommutesWithFilteredColimits.diagram`, for the unshifted
diagram: morphisms from `s` (bounded above by `b`) to `Y` only see the truncation `τ_{< k} Y`
for `k > b`. -/
lemma isCoyonedaColimit_of_isGE {s : DerivedCategory C}
    (hs : HomCommutesWithFilteredColimits.{w} s) (b : ℤ) [s.IsLE b] {I : Type w}
    [SmallCategory I] [IsFiltered I] {Y : I ⥤ DerivedCategory C} (c : Cocone Y) (a : ℤ)
    (hY : ∀ i, (Y.obj i).IsGE a) (hc : c.pt.IsGE a)
    (hH : ∀ n : ℤ, Nonempty (IsColimit ((homologyFunctor C n).mapCocone c))) :
    c.IsCoyonedaColimit s := by
  let k := max a b + 1
  have hbij (X : DerivedCategory C) :
      Function.Bijective fun f : s ⟶ (t.truncLT k).obj X ↦ f ≫ (t.truncLTι k).app X := by
    have : (((t.truncGE k).obj X)⟦(-1 : ℤ)⟧).IsGE (k + 1) :=
      t.isGE_shift _ k (-1) (k + 1) (by lia)
    exact bijective_comp_mor₁ _ (t.triangleLTGE_distinguished k X) s
      (fun f ↦ t.zero_of_isLE_of_isGE f b k (by lia) inferInstance inferInstance)
      (fun f ↦ t.zero_of_isLE_of_isGE f b (k + 1) (by lia) inferInstance this)
  have hle (X : DerivedCategory C) : ((t.truncLT k).obj X).IsLE (a + ((k - 1 - a).toNat : ℕ)) :=
    t.isLE_of_le _ (k - 1) _ (by lia)
  refine IsCoyonedaColimit.of_hom (c' := (t.truncLT k).mapCocone c)
    { app i := (t.truncLTι k).app (Y.obj i)
      naturality _ _ f := (t.truncLTι k).naturality (Y.map f) }
    ((t.truncLTι k).app c.pt) (fun i ↦ (t.truncLTι k).naturality (c.ι.app i))
    (fun i ↦ (hbij _).2) (hbij _)
    (isCoyonedaColimit_of_isGE_of_isLE (k - 1 - a).toNat s hs a _
      (fun i ↦ by have := hY i; exact (inferInstance : ((t.truncLT k).obj (Y.obj i)).IsGE a))
      (fun i ↦ hle _) (by have := hc; exact (inferInstance : ((t.truncLT k).obj c.pt).IsGE a))
      (hle _) (isColimit_homologyFunctor_mapCocone_truncLT hH k))

/-- For `s` bounded above, the continuity of `Hom(s, -[q])` extends from filtered colimits of
objects of `C` to filtered diagrams `Yᵢ` of uniformly bounded below objects of `D(C)` with a
cocone `Y` which induces colimits on all cohomology objects: by induction on the amplitude along
the truncation triangles, `Hom(s, -[q])` only seeing a bounded window of degrees. -/
lemma diagram {s : DerivedCategory C} (hs : HomCommutesWithFilteredColimits.{w} s) (b : ℤ)
    [s.IsLE b] (I : Type w) [SmallCategory I] [IsFiltered I] (Y : I ⥤ DerivedCategory C)
    (c : Cocone Y) (a : ℤ) (hY : ∀ i, (Y.obj i).IsGE a) (hc : c.pt.IsGE a)
    (hH : ∀ n : ℤ, Nonempty (IsColimit ((homologyFunctor C n).mapCocone c))) (q : ℤ) :
    (∀ f : s ⟶ (shiftFunctor _ q).obj c.pt, ∃ (i : I) (g : s ⟶ (shiftFunctor _ q).obj (Y.obj i)),
      f = g ≫ (shiftFunctor _ q).map (c.ι.app i)) ∧
    (∀ (i : I) (g : s ⟶ (shiftFunctor _ q).obj (Y.obj i)),
      g ≫ (shiftFunctor _ q).map (c.ι.app i) = 0 →
        ∃ (j : I) (t : i ⟶ j), g ≫ (shiftFunctor _ q).map (Y.map t) = 0) := by
  have : ((shiftFunctor _ (-q)).obj s).IsLE (b + q) := t.isLE_shift s b (-q) (b + q) (by lia)
  exact (IsCoyonedaColimit.adjunction_iff
    (shiftEquiv' (DerivedCategory C) (-q) q (by lia)).toAdjunction s c).1
      (isCoyonedaColimit_of_isGE (hs.shift (-q)) (b + q) c a hY hc hH)

/-- `HomCommutesWithFilteredColimits.diagram` for a filtered colimit `K = colim Kⱼ` of cochain
complexes all of which vanish below a fixed degree `a`, indexed by a small category `J` in `Type`
(colimits of shape `AsSmall J` being exact in `C`): for `s` bounded above, every morphism
`s ⟶ K[q]` factors through some `Kⱼ[q]`, and two morphisms `s ⟶ Kⱼ[q]` with the same image in
`Hom(s, K[q])` agree in some `Hom(s, Kⱼ'[q])`. -/
lemma cochainComplex {s : DerivedCategory C} (hs : HomCommutesWithFilteredColimits.{w} s)
    (b : ℤ) [s.IsLE b] {J : Type} [SmallCategory J] [IsFiltered J]
    [HasColimitsOfShape (AsSmall.{w} J) C] [HasExactColimitsOfShape (AsSmall.{w} J) C]
    (K : J ⥤ CochainComplex C ℤ) (a : ℤ) (hK : ∀ j, (K.obj j).IsStrictlyGE a) (c : Cocone K)
    (hc : IsColimit c) (q : ℤ) :
    (∀ f : s ⟶ (shiftFunctor _ q).obj (Q.obj c.pt),
      ∃ (j : J) (g : s ⟶ (shiftFunctor _ q).obj (Q.obj (K.obj j))),
        f = g ≫ (shiftFunctor _ q).map (Q.map (c.ι.app j))) ∧
    (∀ (j : J) (g g' : s ⟶ (shiftFunctor _ q).obj (Q.obj (K.obj j))),
      g ≫ (shiftFunctor _ q).map (Q.map (c.ι.app j)) =
          g' ≫ (shiftFunctor _ q).map (Q.map (c.ι.app j)) →
        ∃ (j' : J) (t : j ⟶ j'),
          g ≫ (shiftFunctor _ q).map (Q.map (K.map t)) =
            g' ≫ (shiftFunctor _ q).map (Q.map (K.map t))) := by
  have : IsFiltered (AsSmall.{w} J) := IsFiltered.of_equivalence AsSmall.equiv
  have hc' : IsColimit (c.whisker AsSmall.down) := hc.whiskerEquivalence AsSmall.equiv.symm
  have hpt : c.pt.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) i) hc').isZero_pt
      (Functor.isZero _ fun j ↦ (K.obj _).isZero_of_isStrictlyGE a i hi)
  have hH (n : ℤ) : Nonempty (IsColimit ((homologyFunctor C n).mapCocone
      (Q.mapCocone (c.whisker AsSmall.down)))) :=
    ⟨(IsColimit.mapCoconeEquiv (homologyFunctorFactors C n).symm
      (isColimitOfPreserves (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
        hc')).ofIsoColimit (Cocone.ext (Iso.refl _))⟩
  obtain ⟨h₁, h₂⟩ := hs.diagram b (AsSmall.{w} J) _ (Q.mapCocone (c.whisker AsSmall.down)) a
    (fun j ↦ by
      have := hK (AsSmall.down.obj j)
      exact (inferInstance : (Q.obj (K.obj (AsSmall.down.obj j))).IsGE a))
    (inferInstance : (Q.obj c.pt).IsGE a) hH q
  refine ⟨fun f ↦ ?_, fun j g g' h ↦ ?_⟩
  · obtain ⟨j, g, hg⟩ := h₁ f
    exact ⟨AsSmall.down.obj j, g, hg⟩
  · obtain ⟨j', t, ht⟩ := h₂ ⟨j⟩ (g - g') (by rw [sub_comp, sub_eq_zero]; exact h)
    rw [sub_comp, sub_eq_zero] at ht
    exact ⟨AsSmall.down.obj j', AsSmall.down.map t, ht⟩


variable {C' : Type*} [Category* C'] [Abelian C'] [HasDerivedCategory C']

/-- Transport along an adjunction `F ⊣ G` of triangulated functors: if `G` sends objects of `C'`
placed in degree `0` to objects of `D(C)` concentrated in degrees `≥ a`, and commutes on
cohomology with filtered colimits of objects of `C'`, then `F` preserves bounded above objects
whose morphisms commute with filtered colimits. -/
lemma of_adjunction {F : DerivedCategory C ⥤ DerivedCategory C'}
    {G : DerivedCategory C' ⥤ DerivedCategory C} (adj : F ⊣ G) [G.CommShift ℤ] (a : ℤ)
    (hG : ∀ B : C', (G.obj ((singleFunctor C' 0).obj B)).IsGE a)
    (hGc : ∀ (I : Type w) [SmallCategory I] [IsFiltered I] (B : I ⥤ C') (c : Cocone B)
      (_ : IsColimit c) (n : ℤ),
      Nonempty (IsColimit ((homologyFunctor C n).mapCocone
        ((singleFunctor C' 0 ⋙ G).mapCocone c))))
    {s : DerivedCategory C} (hs : HomCommutesWithFilteredColimits.{w} s) (b : ℤ) [s.IsLE b] :
    HomCommutesWithFilteredColimits.{w} (F.obj s) := by
  intro I _ _ B c hc n
  have := adj.isLeftAdjoint
  have := adj.isRightAdjoint
  refine (IsCoyonedaColimit.adjunction_iff adj s ((singleFunctor C' n).mapCocone c)).2
    (IsCoyonedaColimit.mapCocone_of_iso c (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (G.commShiftIso (-n)).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((singleFunctors C').shiftIso (-n) n 0 (by lia)) G)
      (diagram hs b I (B ⋙ singleFunctor C' 0 ⋙ G) ((singleFunctor C' 0 ⋙ G).mapCocone c) a
        (fun i ↦ hG (B.obj i)) (hG c.pt) (hGc I B c hc) (-n)))

/-- Transport along an adjunction `f ⊣ g` of exact functors of abelian categories, the right
adjoint `g` preserving filtered colimits: the levelwise functor `D(f)` preserves objects whose
morphisms commute with filtered colimits. -/
lemma mapDerivedCategory {f : C ⥤ C'} {g : C' ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    (hg : ∀ (I : Type w) [SmallCategory I] [IsFiltered I], PreservesColimitsOfShape I g)
    {s : DerivedCategory C} (hs : HomCommutesWithFilteredColimits.{w} s) :
    HomCommutesWithFilteredColimits.{w} (f.mapDerivedCategory.obj s) := by
  intro I _ _ B c hc n
  have := hg I
  let : CatCommSq (f.mapHomologicalComplex (ComplexShape.up ℤ)) Q Q f.mapDerivedCategory :=
    ⟨f.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (g.mapHomologicalComplex (ComplexShape.up ℤ)) Q Q g.mapDerivedCategory :=
    ⟨g.mapDerivedCategoryFactors.symm⟩
  let adj' := (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) Q
    (HomologicalComplex.quasiIso C' (ComplexShape.up ℤ)) f.mapDerivedCategory
    g.mapDerivedCategory
  have := adj'.isLeftAdjoint
  have := adj'.isRightAdjoint
  exact (IsCoyonedaColimit.adjunction_iff adj' s ((singleFunctor C' n).mapCocone c)).2
    (IsCoyonedaColimit.mapCocone_of_iso c (g.mapDerivedCategorySingleFunctor n).symm
      (hs I (B ⋙ g) (g.mapCocone c) (isColimitOfPreserves g hc) n))

end HomCommutesWithFilteredColimits

end DerivedCategory
