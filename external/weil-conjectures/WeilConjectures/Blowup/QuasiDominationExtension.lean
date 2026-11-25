/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Density
public import WeilConjectures.Blowup.PartialSectionExtension
public import WeilConjectures.Blowup.QuasiDomination

/-!

# Extending a quasi-domination after an admissible blow-up

Let `x : X ⟶ S` and `y : Y ⟶ S` be morphisms of schemes, with `X` quasi-compact and
quasi-separated and `y` separated and of finite type. Let `U ≤ V` be dense quasi-compact opens
of `X` and let `f : U ⟶ Y` be an `S`-morphism which quasi-dominates `V` over `Y`, i.e. whose
graph is closed in `Y ×ₛ V`. Then there is a `V`-admissible blow-up `X' ⟶ X` and a
quasi-domination of `X'` over `Y` extending `f`.

This is **Conrad's Theorem 2.4** in the form in which it is stated, over an auxiliary base `S`.
It is deduced from the form reduced to the base `X`,
`AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection`, by Conrad's first step:
replace `Y` by `Y ×ₛ X`, so that `f` becomes a partial section of `Y ×ₛ X ⟶ X`.

Reference: Brian Conrad, *Deligne's notes on Nagata compactifications*, Theorem 2.4.

## Main results

- `AlgebraicGeometry.exists_admissibleBlowup_quasiDomination_extends`: the statement above
  (blueprint: `theorem-extension-partial-section--1`).

-/

public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `theorem-extension-partial-section--1`: **extension of a partial section after an
admissible blow-up** (Conrad's Theorem 2.4).

Let `X` be a quasi-compact, quasi-separated `S`-scheme and let `y : Y ⟶ S` be separated and of
finite type. Let `U ≤ V` be quasi-compact opens of `X` with `U` dense (hence `V` dense), and let
`f : U ⟶ Y` be an `S`-morphism which quasi-dominates `V` over `Y`: its graph
`U ⟶ Y ×ₛ V` has closed range. Then there is a `V`-admissible blow-up `π : X' ⟶ X` and a
quasi-domination of `X'` over `Y` extending `(π ∣_ U) ≫ f`.

The proof replaces `Y` by `Y ×ₛ X` and applies the reduced form
`AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection`. The blueprint also assumes
`Y` quasi-compact and quasi-separated; this is not needed. -/
theorem exists_admissibleBlowup_quasiDomination_extends {S X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (x : X ⟶ S) (y : Y ⟶ S) [IsSeparated y] [LocallyOfFiniteType y]
    [QuasiCompact y] {U V : X.Opens} (hUV : U ≤ V) (hU : IsCompact (U : Set X))
    (hV : IsCompact (V : Set X)) (hUdense : Dense (U : Set X)) (f : U.toScheme ⟶ Y)
    (hf : f ≫ y = U.ι ≫ x)
    (hfc : IsClosed (Set.range (pullback.lift (f := y) (g := V.ι ≫ x) f (X.homOfLE hUV)
      (by rw [hf, Scheme.homOfLE_ι_assoc])))) :
    ∃ (B : IsAdmissible X V) (q : QuasiDomination (B.I.blowupMap ≫ x) y),
      q.Extends ((B.I.blowupMap ∣_ U) ≫ f) := by
  -- Conrad's reduction `Y ⇝ Y ×ₛ X`: `f` becomes a section of `pullback.snd y x`.
  have : CompactSpace (pullback y x : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd y x)
  have : QuasiSeparatedSpace (pullback y x : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd y x)
  set f₀ : U.toScheme ⟶ pullback y x := pullback.lift f U.ι hf with hf₀def
  have hf₀ : f₀ ≫ pullback.snd y x = U.ι := pullback.lift_snd _ _ _
  -- the graph over `V` is the graph over `X`, read in the open `pullback.snd y x ⁻¹ᵁ V`
  have hfc₀ : IsClosed ((pullback.snd y x ⁻¹ᵁ V).ι ⁻¹' Set.range f₀) := by
    let e : pullback y (V.ι ≫ x) ≅ (pullback.snd y x ⁻¹ᵁ V).toScheme :=
      (pullbackLeftPullbackSndIso y x V.ι).symm ≪≫
        pullbackRestrictIsoRestrict (pullback.snd y x) V
    set k := pullback.lift (f := y) (g := V.ι ≫ x) f (X.homOfLE hUV)
      (by rw [hf, Scheme.homOfLE_ι_assoc]) ≫ e.hom with hkdef
    have hk : k ≫ (pullback.snd y x ⁻¹ᵁ V).ι = f₀ := by
      refine pullback.hom_ext ?_ ?_ <;>
        simp only [hkdef, e, hf₀def, Iso.trans_hom, Iso.symm_hom, Category.assoc,
          pullbackRestrictIsoRestrict_hom_ι, pullbackLeftPullbackSndIso_inv_fst,
          pullbackLeftPullbackSndIso_inv_fst_snd, pullback.lift_fst, pullback.lift_snd_assoc,
          pullback.lift_snd, Scheme.homOfLE_ι]
    have hrange : (pullback.snd y x ⁻¹ᵁ V).ι ⁻¹' Set.range f₀ = Set.range k := by
      rw [← hk, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.preimage_image_eq _ (pullback.snd y x ⁻¹ᵁ V).ι.isOpenEmbedding.injective]
    rw [hrange, hkdef, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact e.hom.isClosedEmbedding.isClosedMap _ hfc
  obtain ⟨B, W, hUW, g, hg, hgU, hcl⟩ :=
    exists_admissibleBlowup_extend_partialSection hUV hU hV hUdense f₀ hf₀ hfc₀
  have hcomm : (g ≫ pullback.fst y x) ≫ y = W.ι ≫ B.I.blowupMap ≫ x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg, Category.assoc]
  -- the graph over `S` is the graph over `X`, transported along
  -- `(Y ×ₛ X) ×ₓ X' ≅ Y ×ₛ X'`
  have hgraph : pullback.lift (g ≫ pullback.fst y x) W.ι hcomm =
      pullback.lift g W.ι hg ≫ (pullbackLeftPullbackSndIso y x B.I.blowupMap).hom := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
        pullbackLeftPullbackSndIso_hom_snd, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.lift_snd]
  refine ⟨B, ⟨W, (B.dense_coe_preimage_blowupMap hUdense).mono hUW, g ≫ pullback.fst y x,
    hcomm, ?_⟩, hUW, ?_⟩
  · rw [hgraph, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (pullbackLeftPullbackSndIso y x B.I.blowupMap).hom.isClosedEmbedding.isClosedMap _
      hcl
  · rw [reassoc_of% hgU, hf₀def, pullback.lift_fst]

end AlgebraicGeometry
