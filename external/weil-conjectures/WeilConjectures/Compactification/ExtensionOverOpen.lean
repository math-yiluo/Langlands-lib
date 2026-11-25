/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!

# Compactifications which are isomorphisms over an open

Let `F : A ⟶ Z` be a separated, quasi-compact morphism locally of finite type to a
quasi-compact quasi-separated scheme, and let `ι : V ⟶ Z` be a quasi-compact open immersion
over which `F` is an open immersion: `F ⁻¹ V ⟶ V` is an open immersion. Then `F` factors as an
open immersion `A ⟶ B` followed by a proper morphism `p : B ⟶ Z` which is an isomorphism over
`V` (`AlgebraicGeometry.exists_isProper_isPullback_of_isOpenImmersion`).

The construction glues `A` and `V` along `F ⁻¹ V` (a pushout of open immersions), which is
separated over `Z` since the graph of `F ⁻¹ V ⟶ V` is an isomorphism, takes a dense
compactification `B` of the glued scheme over `Z` (Nagata), and observes that the section
`V ⟶ p ⁻¹ V` is an open and closed immersion with dense image, hence an isomorphism.

More generally, `V` may be a closed subscheme of an open `Z° ⊆ Z` containing the image of
`F ⁻¹ Z°` (`AlgebraicGeometry.exists_isProper_isPullback_of_isClosedImmersion`): then `B` is `V`
over `Z°`, and `A ∪ V` is dense in `B`. Such density statements identify inverse images of opens
(`AlgebraicGeometry.isPullback_id_of_dense`): an open `N ⊆ B` over an open `N ⊆ X` along a
separated `B ⟶ X` is the whole inverse image as soon as a dense subset of `B` meets the inverse
image only in `N`, the section `N ⟶ B ×_X N` being open, closed and dense.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {A A' V Z : Scheme.{u}} {F : A ⟶ Z} {ι : V ⟶ Z} {a : A' ⟶ A} {F' : A' ⟶ V}

/-- **Compactification which is an isomorphism over an open.** Let `F : A ⟶ Z` be separated,
quasi-compact and locally of finite type, `Z` quasi-compact and quasi-separated, and let
`ι : V ⟶ Z` be a quasi-compact open immersion such that the base change `F' : A' ⟶ V` of `F`
along `ι` is an open immersion. Then there are an open immersion `c : A ⟶ B` and a proper
morphism `p : B ⟶ Z` with `c ≫ p = F`, and a section `s : V ⟶ B` extending `c` on `A'`, which
identifies `V` with the inverse image `p ⁻¹ V`. -/
theorem exists_isProper_isPullback_of_isOpenImmersion [CompactSpace Z] [QuasiSeparatedSpace Z]
    [IsSeparated F] [QuasiCompact F] [LocallyOfFiniteType F] [IsOpenImmersion ι] [QuasiCompact ι]
    [IsOpenImmersion a] [IsOpenImmersion F'] (H : IsPullback a F' F ι) :
    ∃ (B : Scheme.{u}) (c : A ⟶ B) (p : B ⟶ Z) (s : V ⟶ B), IsOpenImmersion c ∧ IsProper p ∧
      c ≫ p = F ∧ a ≫ c = F' ≫ s ∧ IsPullback s (𝟙 V) p ι := by
  have w : a ≫ F = F' ≫ ι := H.w
  have hgraph : IsClosedImmersion (pullback.lift a F' w) := by
    have : pullback.lift a F' w = H.isoPullback.hom := by
      apply pullback.hom_ext <;> simp
    rw [this]
    infer_instance
  have : IsSeparated (pushout.desc F ι w) := IsSeparated.pushout_desc a F' w hgraph
  have : QuasiCompact (pushout.desc F ι w) := QuasiCompact.pushout_desc a F' w
  have : LocallyOfFiniteType (pushout.desc F ι w) :=
    IsZariskiLocalAtSource.pushout_desc a F' w ‹_› inferInstance
  let c₁ := denseCompactification (pushout.desc F ι w)
  have : IsSchemeTheoreticallyDominant c₁.i := denseCompactification_isDense _
  have : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion_iff.mpr inferInstance
  refine ⟨c₁.Z, pushout.inl a F' ≫ c₁.i, c₁.g, pushout.inr a F' ≫ c₁.i, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← c₁.comm, pushout.inl_desc]
  · rw [pushout.condition_assoc]
  have hs : (pushout.inr a F' ≫ c₁.i) ≫ c₁.g = 𝟙 V ≫ ι := by
    rw [Category.assoc, ← c₁.comm, pushout.inr_desc, Category.id_comp]
  let l : V ⟶ pullback c₁.g ι := pullback.lift _ _ hs
  have : IsClosedImmersion (l ≫ pullback.snd c₁.g ι) := by
    rw [pullback.lift_snd]
    infer_instance
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.snd c₁.g ι)
  have : IsOpenImmersion (l ≫ pullback.fst c₁.g ι) := by
    rw [pullback.lift_fst]
    infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (pullback.fst c₁.g ι)
  have hsurj : Function.Surjective l := by
    by_contra hns
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Set.range l := by simpa [Function.Surjective] using hns
    have hO : IsOpen ((pullback.fst c₁.g ι) '' (Set.range l)ᶜ) :=
      (pullback.fst c₁.g ι).isOpenEmbedding.isOpenMap _
        l.isClosedEmbedding.isClosed_range.isOpen_compl
    obtain ⟨y, x', hx', hxy⟩ := c₁.i.denseRange.exists_mem_open hO ⟨_, x, hx, rfl⟩
    have key : ∃ v, pushout.inr a F' v = y := by
      have hy : y ∈ Set.range (pushout.inl a F') ∪ Set.range (pushout.inr a F') := by
        rw [range_pushout_inl_union_range_pushout_inr]
        trivial
      obtain ⟨b, rfl⟩ | h := hy
      · have hb : F b = ι (pullback.snd c₁.g ι x') := by
          rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hxy,
            ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← c₁.comm, pushout.inl_desc]
        obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hb
        refine ⟨F' (H.isoPullback.inv z), ?_⟩
        rw [← Scheme.Hom.comp_apply, ← pushout.condition, Scheme.Hom.comp_apply,
          ← Scheme.Hom.comp_apply H.isoPullback.inv a, H.isoPullback_inv_fst, hz]
      · exact h
    obtain ⟨v, rfl⟩ := key
    refine hx' ⟨v, (pullback.fst c₁.g ι).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, hxy, Scheme.Hom.comp_apply]
  have : IsIso l := (isIso_iff_isOpenImmersion_and_surjective l).2 ⟨inferInstance, ⟨hsurj⟩⟩
  exact IsPullback.of_iso_pullback ⟨hs⟩ (asIso l) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

/-- A point of `X` whose image under `f` lies in the image of `g` lifts along the first
projection of a pullback square of `f` and `g`. -/
lemma Scheme.Pullback.mem_range_fst_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback fst snd f g) {x : X}
    (hx : f x ∈ Set.range g) : x ∈ Set.range fst := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
  exact ⟨H.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, hz]⟩

/-- A morphism of schemes which is both an open and a closed immersion and has dense range is an
isomorphism. -/
lemma isIso_of_isOpenImmersion_of_isClosedImmersion {X Y : Scheme.{u}} (l : X ⟶ Y)
    [IsOpenImmersion l] [IsClosedImmersion l] (hl : Dense (Set.range l)) : IsIso l := by
  have hsurj : Function.Surjective l := by
    rw [← Set.range_eq_univ, ← l.isClosedEmbedding.isClosed_range.closure_eq]
    exact hl.closure_eq
  exact (isIso_iff_isOpenImmersion_and_surjective l).2 ⟨inferInstance, ⟨hsurj⟩⟩

/-- Let `c : N ⟶ B` and `h : N ⟶ X` be open immersions and `π : B ⟶ X` a separated morphism
with `c ≫ π = h`. If a dense subset `D ⊆ B` meets the inverse image of `h(N)` only in `c(N)`,
then `N` is the inverse image of `h(N)` along `π`: the section `N ⟶ π ⁻¹ h(N)` is open, closed
and has dense range. -/
lemma isPullback_id_of_dense {N B X : Scheme.{u}} {c : N ⟶ B} {π : B ⟶ X} {h : N ⟶ X}
    [IsOpenImmersion c] [IsOpenImmersion h] [IsSeparated π] (w : c ≫ π = h) {D : Set B}
    (hD : Dense D) (hDc : ∀ b ∈ D, π b ∈ Set.range h → b ∈ Set.range c) :
    IsPullback c (𝟙 N) π h := by
  have w' : c ≫ π = 𝟙 N ≫ h := by rw [w, Category.id_comp]
  let l : N ⟶ pullback π h := pullback.lift c (𝟙 N) w'
  have : IsClosedImmersion (l ≫ pullback.snd π h) := by
    rw [pullback.lift_snd]
    infer_instance
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.snd π h)
  have : IsOpenImmersion (l ≫ pullback.fst π h) := by
    rw [pullback.lift_fst]
    infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (pullback.fst π h)
  have : IsIso l := by
    refine isIso_of_isOpenImmersion_of_isClosedImmersion l
      ((hD.preimage (pullback.fst π h).isOpenEmbedding.isOpenMap).mono ?_)
    intro x hx
    obtain ⟨n, hn⟩ := hDc _ hx ⟨pullback.snd π h x, by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
    refine ⟨n, (pullback.fst π h).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, hn]
  exact IsPullback.of_iso_pullback ⟨w'⟩ (asIso l) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

/-- **Compactification which is an isomorphism over a locally closed subscheme.** Let
`F : A ⟶ Z` be separated, quasi-compact and locally of finite type, `Z` quasi-compact and
quasi-separated, `ιo : Z° ⟶ Z` a quasi-compact open immersion and `κ : V ⟶ Z°` a closed
immersion, such that the inverse image `A' = F ⁻¹ Z°` maps into `V` by an open immersion
`F' : A' ⟶ V`. Then there are an open immersion `c : A ⟶ B` and a proper morphism
`p : B ⟶ Z` with `c ≫ p = F`, and a section `s : V ⟶ B` extending `c` on `A'`, which identifies
`V` with the inverse image `p ⁻¹ Z°`; moreover `c(A) ∪ s(V)` is dense in `B`. -/
theorem exists_isProper_isPullback_of_isClosedImmersion {Z' : Scheme.{u}} {ιo : Z' ⟶ Z}
    {κ : V ⟶ Z'} [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated F] [QuasiCompact F]
    [LocallyOfFiniteType F] [IsOpenImmersion ιo] [QuasiCompact ιo] [IsClosedImmersion κ]
    [IsOpenImmersion a] [IsOpenImmersion F'] (H : IsPullback a (F' ≫ κ) F ιo) :
    ∃ (B : Scheme.{u}) (c : A ⟶ B) (p : B ⟶ Z) (s : V ⟶ B), IsOpenImmersion c ∧ IsProper p ∧
      c ≫ p = F ∧ a ≫ c = F' ≫ s ∧ IsPullback s κ p ιo ∧
      Dense (Set.range c ∪ Set.range s) := by
  have H' : IsPullback a F' F (κ ≫ ιo) := by
    have := ((IsPullback.id_vert F').paste_horiz (IsKernelPair.id_of_mono κ)).paste_vert H.flip
    rw [Category.comp_id, Category.id_comp] at this
    exact this.flip
  have w : a ≫ F = F' ≫ κ ≫ ιo := H'.w
  have hgraph : IsClosedImmersion (pullback.lift a F' w) := by
    have : pullback.lift a F' w = H'.isoPullback.hom := by
      apply pullback.hom_ext <;> simp
    rw [this]
    infer_instance
  have : IsSeparated (pushout.desc F (κ ≫ ιo) w) := IsSeparated.pushout_desc a F' w hgraph
  have : QuasiCompact (pushout.desc F (κ ≫ ιo) w) := QuasiCompact.pushout_desc a F' w
  have : LocallyOfFiniteType (pushout.desc F (κ ≫ ιo) w) :=
    IsZariskiLocalAtSource.pushout_desc a F' w ‹_› inferInstance
  let c₁ := denseCompactification (pushout.desc F (κ ≫ ιo) w)
  have : IsSchemeTheoreticallyDominant c₁.i := denseCompactification_isDense _
  have : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion_iff.mpr inferInstance
  have hrange : Set.range (pushout.inl a F' ≫ c₁.i) ∪ Set.range (pushout.inr a F' ≫ c₁.i) =
      Set.range c₁.i := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp, ← Set.image_union,
      range_pushout_inl_union_range_pushout_inr, Set.image_univ]
  refine ⟨c₁.Z, pushout.inl a F' ≫ c₁.i, c₁.g, pushout.inr a F' ≫ c₁.i, inferInstance,
    inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← c₁.comm, pushout.inl_desc]
  · rw [pushout.condition_assoc]
  · have hs : (pushout.inr a F' ≫ c₁.i) ≫ c₁.g = κ ≫ ιo := by
      rw [Category.assoc, ← c₁.comm, pushout.inr_desc]
    let l : V ⟶ pullback c₁.g ιo := pullback.lift _ _ hs
    have : IsClosedImmersion (l ≫ pullback.snd c₁.g ιo) := by
      rw [pullback.lift_snd]
      infer_instance
    have : IsClosedImmersion l := IsClosedImmersion.of_comp l (pullback.snd c₁.g ιo)
    have : IsOpenImmersion (l ≫ pullback.fst c₁.g ιo) := by
      rw [pullback.lift_fst]
      infer_instance
    have : IsOpenImmersion l := IsOpenImmersion.of_comp l (pullback.fst c₁.g ιo)
    have : IsIso l := by
      refine isIso_of_isOpenImmersion_of_isClosedImmersion l
        ((c₁.i.denseRange.preimage (pullback.fst c₁.g ιo).isOpenEmbedding.isOpenMap).mono ?_)
      rintro x ⟨y, hxy⟩
      obtain ⟨v, rfl⟩ : ∃ v, pushout.inr a F' v = y := by
        have hy : y ∈ Set.range (pushout.inl a F') ∪ Set.range (pushout.inr a F') := by
          rw [range_pushout_inl_union_range_pushout_inr]
          trivial
        obtain ⟨b, rfl⟩ | h := hy
        · have hb : F b = ιo (pullback.snd c₁.g ιo x) := by
            rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, ← hxy,
              ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← c₁.comm, pushout.inl_desc]
          obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hb
          refine ⟨F' (H.isoPullback.inv z), ?_⟩
          rw [← Scheme.Hom.comp_apply, ← pushout.condition, Scheme.Hom.comp_apply,
            ← Scheme.Hom.comp_apply H.isoPullback.inv a, H.isoPullback_inv_fst, hz]
        · exact h
      refine ⟨v, (pullback.fst c₁.g ιo).isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hxy]
    exact IsPullback.of_iso_pullback ⟨hs⟩ (asIso l) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
  · rw [hrange]
    exact c₁.i.denseRange

end AlgebraicGeometry
