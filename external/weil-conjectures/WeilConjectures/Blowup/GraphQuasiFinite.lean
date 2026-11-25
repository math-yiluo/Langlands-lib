/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.QuasiAffineGeneral

/-!

# Conrad's Theorem 2.4, general case: the closed graph is quasi-finite over the blow-up

This file proves the construction half of the General Case of Theorem 2.4 in Conrad's
*Deligne's notes on Nagata compactifications* (blueprint:
`lemma:nagata-conrad-graph-closure-quasi-finite`): for a separated morphism `p : Y ⟶ X`
locally of finite type between qcqs schemes and a section `f` of `p` over a quasi-compact
open `U` whose image is closed over a larger quasi-compact open `V`, there is a
`V`-admissible blow-up `q : X̃ ⟶ X` such that the scheme-theoretic image of the graph
`F = (f, σ) : U ⟶ Y ×[X] X̃` is quasi-finite and separated over `X̃`.

## Main results

- `AlgebraicGeometry.exists_isAdmissible_extend_of_isAffineOpen_of_le`: Conrad's Case 3
  (`AlgebraicGeometry.exists_isAdmissible_extend_of_isQuasiAffineHom_of_le`) applied over
  an affine open `Z` of `Y`.
- `AlgebraicGeometry.exists_isAdmissible_locallyQuasiFinite_image_graph`: the main result.

## Proof sketch

Cover `Y` by finitely many affine opens `Z`. For each of them `Z ⟶ Y ⟶ X` is quasi-affine
as a morphism — the source is affine, hence quasi-affine, and the morphism is quasi-compact
— so Case 3 applies to the restriction of `f` to `U_Z = f ⁻¹ Z`, and produces a
`V`-admissible centre `I_Z` on `X` together with an open `W_Z` of `Bl_{I_Z}(X)` carrying an
extension `g_Z` of `f|_{U_Z}` with closed graph in `Z ×[X] Bl_{I_Z}(X)`.

Unlike Conrad we do **not** restrict to the scheme-theoretic image `X_Z` of `U_Z` in `X`:
Case 3 as proved here carries no density hypothesis, so the restriction — and with it the
extension of the centre from `X_Z` back to `X` and the ambient closedness of the strict
transform — is unnecessary.

Let `I = ∏_Z I_Z` and `q : X̃ = Bl_I(X) ⟶ X`. Each `I_Z` pulls back to an invertible ideal
on `X̃`, so the universal property of blowing up gives a comparison `c_Z : X̃ ⟶ Bl_{I_Z}(X)`
over `X`, and the closed graph of `g_Z` pulls back to a closed subset of the open
`(pr_Y) ⁻¹ Z` of `Y ×[X] X̃` which is a section over an open of `X̃`
(`AlgebraicGeometry.isClosed_preimage_range_lift_of_comp`). Since these opens cover
`Y ×[X] X̃` and the closure of the range of `F` meets each of them inside the corresponding
section, the fibres of `F(U)‾ ⟶ X̃` are finite, whence
`AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton` applies.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-- **Transport of a closed graph along a further blow-up.** Let `π : Bl ⟶ X` and
`q : X' ⟶ X` be two morphisms with `q = c ≫ π`, let `Z` be an open of `Y` and `W` an open
of `Bl`, and let `g : W ⟶ Z` be a morphism over `X` whose graph is closed in `Z ×[X] Bl`.
Then the graph of the induced morphism on `c ⁻¹ W` is closed in the open `(pr_Y) ⁻¹ Z` of
`Y ×[X] X'`.

This is the mechanism behind the finiteness of the fibres in
`AlgebraicGeometry.exists_isAdmissible_locallyQuasiFinite_image_graph`: the base change of
the graph section along `Y ×[X] X' ⟶ Y ×[X] Bl` has as range the preimage of its range. -/
theorem isClosed_preimage_range_lift_of_comp {X Y X' Bl : Scheme.{u}}
    (p : Y ⟶ X) {q : X' ⟶ X} {π : Bl ⟶ X} (c : X' ⟶ Bl) (hc : c ≫ π = q)
    {Z : Y.Opens} {W : Bl.Opens} (g : W.toScheme ⟶ Z.toScheme)
    (hg : g ≫ Z.ι ≫ p = W.ι ≫ π)
    (hcl : IsClosed (Set.range (pullback.lift g W.ι hg)))
    (hcond : ((c ∣_ W) ≫ g ≫ Z.ι) ≫ p = (c ⁻¹ᵁ W).ι ≫ q) :
    IsClosed ((pullback.fst p q ⁻¹ᵁ Z).ι ⁻¹'
      Set.range (pullback.lift ((c ∣_ W) ≫ g ≫ Z.ι) (c ⁻¹ᵁ W).ι hcond)) := by
  have hΩpb : IsPullback (pullback.fst p q ∣_ Z) (pullback.fst p q ⁻¹ᵁ Z).ι Z.ι
      (pullback.fst p q) := isPullback_morphismRestrict (pullback.fst p q) Z
  have hOmegaX : IsPullback (pullback.fst p q ∣_ Z)
      ((pullback.fst p q ⁻¹ᵁ Z).ι ≫ pullback.snd p q) (Z.ι ≫ p) q :=
    hΩpb.paste_vert (IsPullback.of_hasPullback p q)
  have hApb : IsPullback (pullback.fst (Z.ι ≫ p) π) (pullback.snd (Z.ι ≫ p) π) (Z.ι ≫ p) π :=
    IsPullback.of_hasPullback _ _
  have hτcond : (pullback.fst p q ∣_ Z) ≫ (Z.ι ≫ p) =
      ((pullback.fst p q ⁻¹ᵁ Z).ι ≫ pullback.snd p q ≫ c) ≫ π := by
    have h := hOmegaX.w
    simp only [Category.assoc] at h ⊢
    rw [hc]
    exact h
  set τ : (pullback.fst p q ⁻¹ᵁ Z).toScheme ⟶ pullback (Z.ι ≫ p) π :=
    pullback.lift (pullback.fst p q ∣_ Z)
      ((pullback.fst p q ⁻¹ᵁ Z).ι ≫ pullback.snd p q ≫ c) hτcond with hτdef
  have hτfst : τ ≫ pullback.fst (Z.ι ≫ p) π = pullback.fst p q ∣_ Z := pullback.lift_fst _ _ _
  have hτsnd : τ ≫ pullback.snd (Z.ι ≫ p) π =
      (pullback.fst p q ⁻¹ᵁ Z).ι ≫ pullback.snd p q ≫ c := pullback.lift_snd _ _ _
  have hτpb : IsPullback ((pullback.fst p q ⁻¹ᵁ Z).ι ≫ pullback.snd p q) τ c
      (pullback.snd (Z.ι ≫ p) π) := by
    refine IsPullback.of_bot ?_ ?_ hApb.flip
    · rw [hτfst, hc]
      exact hOmegaX.flip
    · rw [hτsnd, ← Category.assoc]
  -- the section over `c ⁻¹ W` and its factorization through the open `(pr_Y) ⁻¹ Z`
  have hΦfst : pullback.lift ((c ∣_ W) ≫ g ≫ Z.ι) (c ⁻¹ᵁ W).ι hcond ≫ pullback.fst p q =
      (c ∣_ W) ≫ g ≫ Z.ι := pullback.lift_fst _ _ _
  have hΦsnd : pullback.lift ((c ∣_ W) ≫ g ≫ Z.ι) (c ⁻¹ᵁ W).ι hcond ≫ pullback.snd p q =
      (c ⁻¹ᵁ W).ι := pullback.lift_snd _ _ _
  have hφcond : ((c ∣_ W) ≫ g) ≫ Z.ι =
      pullback.lift ((c ∣_ W) ≫ g ≫ Z.ι) (c ⁻¹ᵁ W).ι hcond ≫ pullback.fst p q := by
    rw [hΦfst, Category.assoc]
  set φ : (c ⁻¹ᵁ W).toScheme ⟶ (pullback.fst p q ⁻¹ᵁ Z).toScheme :=
    hΩpb.lift ((c ∣_ W) ≫ g) (pullback.lift ((c ∣_ W) ≫ g ≫ Z.ι) (c ⁻¹ᵁ W).ι hcond) hφcond
    with hφdef
  have hφfst : φ ≫ (pullback.fst p q ∣_ Z) = (c ∣_ W) ≫ g := hΩpb.lift_fst _ _ _
  have hφsnd : φ ≫ (pullback.fst p q ⁻¹ᵁ Z).ι =
      pullback.lift ((c ∣_ W) ≫ g ≫ Z.ι) (c ⁻¹ᵁ W).ι hcond := hΩpb.lift_snd _ _ _
  have hkfst : pullback.lift g W.ι hg ≫ pullback.fst (Z.ι ≫ p) π = g := pullback.lift_fst _ _ _
  have hksnd : pullback.lift g W.ι hg ≫ pullback.snd (Z.ι ≫ p) π = W.ι := pullback.lift_snd _ _ _
  have hφpb : IsPullback (c ∣_ W) φ (pullback.lift g W.ι hg) τ := by
    refine IsPullback.of_bot ?_ ?_ hτpb.flip
    · rw [← Category.assoc φ, hφsnd, hΦsnd, hksnd]
      exact isPullback_morphismRestrict c W
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hkfst, Category.assoc, hτfst]
        exact hφfst.symm
      · rw [Category.assoc, hksnd, morphismRestrict_ι, Category.assoc, hτsnd,
          ← Category.assoc φ, hφsnd, ← Category.assoc, hΦsnd]
  -- the range of the section is the preimage of the closed graph
  have hrange : Set.range φ = τ ⁻¹' Set.range (pullback.lift g W.ι hg) := by
    have hsurj : Function.Surjective ⇑hφpb.isoPullback.hom :=
      (Scheme.homeoOfIso hφpb.isoPullback).surjective
    rw [← hφpb.isoPullback_hom_snd]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [hsurj.range_eq, Set.image_univ, Scheme.Pullback.range_snd]
  have himg : (pullback.fst p q ⁻¹ᵁ Z).ι ⁻¹'
      Set.range (pullback.lift ((c ∣_ W) ≫ g ≫ Z.ι) (c ⁻¹ᵁ W).ι hcond) = Set.range φ := by
    rw [← hφsnd]
    ext t
    simp only [Set.mem_preimage, Set.mem_range, Scheme.Hom.comp_base, TopCat.coe_comp,
      Function.comp_apply]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (pullback.fst p q ⁻¹ᵁ Z).ι.isOpenEmbedding.injective ha⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  rw [himg, hrange]
  exact hcl.preimage τ.continuous

variable {X : Scheme.{u}}

/-- **Conrad's Theorem 2.4, general case, one affine piece.** Under the hypotheses of the
general case, and for `Z` an affine open of `Y`, Case 3
(`AlgebraicGeometry.exists_isAdmissible_extend_of_isQuasiAffineHom_of_le`) applies to the
restriction of `f` to `f ⁻¹ Z`, seen as a section of the quasi-affine morphism
`Z ⟶ Y ⟶ X`: there is a `V`-admissible blow-up of `X`, an open `W` of it containing the
preimage of `f ⁻¹ Z`, and a morphism `g : W ⟶ Z` over `X` extending `f` there and having
closed graph in `Z ×[X] Bl`.

The extension property is stated in the form actually used downstream: every morphism from
`f ⁻¹ Z` into `W` lying over the inclusion `f ⁻¹ Z ↪ X` agrees with `f` after `g`. -/
theorem exists_isAdmissible_extend_of_isAffineOpen_of_le
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    [IsSeparated p] [LocallyOfFiniteType p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f))
    {Z : Y.Opens} (hZ : IsAffineOpen Z) :
    ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (g : W.toScheme ⟶ Z.toScheme)
      (hg : g ≫ Z.ι ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowupMap ⁻¹ᵁ (U.ι ''ᵁ f ⁻¹ᵁ Z) ≤ W ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) ∧
        ∀ m : (f ⁻¹ᵁ Z).toScheme ⟶ W.toScheme,
          m ≫ W.ι ≫ B.I.blowupMap = (f ⁻¹ᵁ Z).ι ≫ U.ι →
            m ≫ g ≫ Z.ι = (f ⁻¹ᵁ Z).ι ≫ f := by
  classical
  have : QuasiCompact p := quasiCompact_of_compactSpace p
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : IsAffine Z.toScheme := hZ
  have : QuasiCompact (Z.ι ≫ p) := quasiCompact_of_compactSpace _
  have hUZU : U.ι ''ᵁ f ⁻¹ᵁ Z ≤ U :=
    (Scheme.Hom.image_le_opensRange U.ι _).trans (le_of_eq U.opensRange_ι)
  have hUZV : U.ι ''ᵁ f ⁻¹ᵁ Z ≤ V := hUZU.trans hUV
  have hUZc : IsCompact ((U.ι ''ᵁ f ⁻¹ᵁ Z : X.Opens) : Set X) := by
    rw [Scheme.Hom.coe_image]
    exact (f.isCompact_preimage hZ.isCompact).image U.ι.continuous
  set eZ : (f ⁻¹ᵁ Z).toScheme ≅ (U.ι ''ᵁ f ⁻¹ᵁ Z).toScheme := U.ι.isoImage (f ⁻¹ᵁ Z) with heZdef
  have hehom : eZ.hom ≫ (U.ι ''ᵁ f ⁻¹ᵁ Z).ι = (f ⁻¹ᵁ Z).ι ≫ U.ι :=
    Scheme.Hom.isoImage_hom_ι U.ι (f ⁻¹ᵁ Z)
  have heinv : eZ.inv ≫ (f ⁻¹ᵁ Z).ι ≫ U.ι = (U.ι ''ᵁ f ⁻¹ᵁ Z).ι :=
    Scheme.Hom.isoImage_inv_ι U.ι (f ⁻¹ᵁ Z)
  set fZ : (U.ι ''ᵁ f ⁻¹ᵁ Z).toScheme ⟶ Z.toScheme := eZ.inv ≫ (f ∣_ Z) with hfZdef
  have hfZ : fZ ≫ Z.ι ≫ p = (U.ι ''ᵁ f ⁻¹ᵁ Z).ι := by
    rw [hfZdef, Category.assoc, ← Category.assoc (f ∣_ Z), morphismRestrict_ι,
      Category.assoc, hf, heinv]
  -- the range of the restricted section, and its closedness over `V`
  have hrfZ : Set.range fZ = ⇑Z.ι ⁻¹' Set.range f := by
    have hsurj : Function.Surjective ⇑eZ.inv := (Scheme.homeoOfIso eZ.symm).surjective
    have h1 : Set.range fZ = Set.range (f ∣_ Z) := by
      rw [hfZdef]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      rw [hsurj.range_eq, Set.image_univ]
    have hpb := isPullback_morphismRestrict f Z
    have hsurj2 : Function.Surjective ⇑hpb.isoPullback.hom :=
      (Scheme.homeoOfIso hpb.isoPullback).surjective
    rw [h1, ← hpb.isoPullback_hom_fst]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rw [hsurj2.range_eq, Set.image_univ, Scheme.Pullback.range_fst]
  have hfcZ : IsClosed ((Z.ι ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ⁻¹' Set.range fZ) := by
    have hset : ⇑(Z.ι ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ⁻¹' (⇑Z.ι ⁻¹' Set.range f) =
        ⇑(Z.ι ∣_ (p ⁻¹ᵁ V)) ⁻¹' (⇑(p ⁻¹ᵁ V).ι ⁻¹' Set.range f) := by
      have h := congrArg (fun t : (Z.ι ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme ⟶ Y => ⇑t ⁻¹' Set.range ⇑f)
        (morphismRestrict_ι Z.ι (p ⁻¹ᵁ V)).symm
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] using h
    rw [hrfZ, hset]
    exact hfc.preimage (Z.ι ∣_ (p ⁻¹ᵁ V)).continuous
  obtain ⟨B, W, hUW, g, hg, hagree, hclosed⟩ :=
    exists_isAdmissible_extend_of_isQuasiAffineHom_of_le (X := X) (U := U.ι ''ᵁ f ⁻¹ᵁ Z)
      (V := V) hUZV hUZc hV (Y := Z.toScheme) (p := Z.ι ≫ p) fZ hfZ hfcZ
  refine ⟨B, W, g, hg, hUW, hclosed, ?_⟩
  intro m hm
  -- `m` factors through the preimage of `U.ι ''ᵁ f ⁻¹ᵁ Z`
  have hmr : Set.range (m ≫ W.ι) ⊆
      Set.range (B.I.blowupMap ⁻¹ᵁ (U.ι ''ᵁ f ⁻¹ᵁ Z)).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    have hmw := congrArg (fun t : (f ⁻¹ᵁ Z).toScheme ⟶ X => t.base w) hm
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hmw
    have hw : (f ⁻¹ᵁ Z).ι.base w ∈ ((f ⁻¹ᵁ Z : U.toScheme.Opens) : Set U.toScheme) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self w
    change B.I.blowupMap.base _ ∈ ((U.ι ''ᵁ f ⁻¹ᵁ Z : X.Opens) : Set X)
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    rw [hmw, Scheme.Hom.coe_image]
    exact ⟨_, hw, rfl⟩
  set m' := IsOpenImmersion.lift (B.I.blowupMap ⁻¹ᵁ (U.ι ''ᵁ f ⁻¹ᵁ Z)).ι (m ≫ W.ι) hmr
    with hm'def
  have hm'ι : m' ≫ (B.I.blowupMap ⁻¹ᵁ (U.ι ''ᵁ f ⁻¹ᵁ Z)).ι = m ≫ W.ι :=
    IsOpenImmersion.lift_fac _ _ _
  have hmfac : m = m' ≫ B.I.blowup.homOfLE hUW := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, hm'ι]
  have hid : m' ≫ (B.I.blowupMap ∣_ (U.ι ''ᵁ f ⁻¹ᵁ Z)) ≫ eZ.inv = 𝟙 (f ⁻¹ᵁ Z).toScheme := by
    rw [← cancel_mono ((f ⁻¹ᵁ Z).ι ≫ U.ι), Category.assoc, Category.assoc, heinv,
      morphismRestrict_ι, ← Category.assoc, hm'ι, Category.assoc, hm, Category.id_comp]
  calc m ≫ g ≫ Z.ι
      = (m' ≫ B.I.blowup.homOfLE hUW) ≫ g ≫ Z.ι := by rw [← hmfac]
    _ = m' ≫ (B.I.blowup.homOfLE hUW ≫ g) ≫ Z.ι := by simp only [Category.assoc]
    _ = m' ≫ ((B.I.blowupMap ∣_ (U.ι ''ᵁ f ⁻¹ᵁ Z)) ≫ fZ) ≫ Z.ι := by rw [hagree]
    _ = (m' ≫ (B.I.blowupMap ∣_ (U.ι ''ᵁ f ⁻¹ᵁ Z)) ≫ eZ.inv) ≫ (f ∣_ Z) ≫ Z.ι := by
          simp only [hfZdef, Category.assoc]
    _ = (f ⁻¹ᵁ Z).ι ≫ f := by rw [hid, Category.id_comp, morphismRestrict_ι]

/-- **Conrad's Theorem 2.4, General Case: the closed graph is quasi-finite over the
blow-up** (blueprint: `lemma:nagata-conrad-graph-closure-quasi-finite`).

"Quasi-finite and separated over `X̃`" is spelled out as the four properties
`LocallyQuasiFinite`, `LocallyOfFiniteType`, `IsSeparated` and `QuasiCompact` of
`F(U)‾ ⟶ X̃`, which are exactly the hypotheses of
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_locallyQuasiFinite` and of
`AlgebraicGeometry.IsQuasiAffineHom.of_locallyQuasiFinite`. -/
theorem exists_isAdmissible_locallyQuasiFinite_image_graph
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    [IsSeparated p] [LocallyOfFiniteType p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ (B : IsAdmissible X V) (σ : U.toScheme ⟶ B.I.blowup),
      IsOpenImmersion σ ∧ σ ≫ B.I.blowupMap = U.ι ∧
      ∀ F : U.toScheme ⟶ pullback p B.I.blowupMap,
        F ≫ pullback.fst p B.I.blowupMap = f →
        F ≫ pullback.snd p B.I.blowupMap = σ →
        LocallyQuasiFinite (F.imageι ≫ pullback.snd p B.I.blowupMap) ∧
          LocallyOfFiniteType (F.imageι ≫ pullback.snd p B.I.blowupMap) ∧
          IsSeparated (F.imageι ≫ pullback.snd p B.I.blowupMap) ∧
          QuasiCompact (F.imageι ≫ pullback.snd p B.I.blowupMap) := by
  classical
  have : QuasiCompact p := quasiCompact_of_compactSpace p
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  -- a finite affine open cover of `Y`
  have hcov : (Set.univ : Set Y) ⊆ ⋃ Z : Y.affineOpens, ((Z : Y.Opens) : Set Y) := by
    intro y _
    have hy : y ∈ (⊤ : Y.Opens) := trivial
    rw [← iSup_affineOpens_eq_top Y] at hy
    obtain ⟨Z, hZ⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact Set.mem_iUnion.mpr ⟨Z, hZ⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun Z : Y.affineOpens => ((Z : Y.Opens) : Set Y)) (fun Z => (Z : Y.Opens).isOpen) hcov
  -- Case 3 over each affine open of `Y`
  choose B W g hg hle hcl hagr using fun Z : Y.affineOpens =>
    exists_isAdmissible_extend_of_isAffineOpen_of_le hUV hU hV f hf hfc Z.2
  -- the product centre
  obtain ⟨I, hIdef⟩ : ∃ I : X.IdealSheafData, I = ∏ Z ∈ s, (B Z).I := ⟨_, rfl⟩
  have hIft : I.ofFiniteType := by
    rw [hIdef]
    exact Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb)
      (by simpa using Scheme.IdealSheafData.ofFiniteType_top) fun Z _ ↦ (B Z).finiteType
  have hIdisj : Disjoint (V : Set X) (I.support : Set X) := by
    rw [hIdef]
    refine Finset.prod_induction _
      (fun J : X.IdealSheafData ↦ Disjoint (V : Set X) (J.support : Set X))
      (fun a b ha hb ↦ ?_) (by simp) fun Z _ ↦ (B Z).disjoint_support
    rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
    exact Set.disjoint_union_right.mpr ⟨ha, hb⟩
  -- the comparison morphisms to the blow-ups of the factors
  have hcex : ∀ Z : Y.affineOpens, Z ∈ s →
      ∃ cc : I.blowup ⟶ (B Z).I.blowup, cc ≫ (B Z).I.blowupMap = I.blowupMap := by
    intro Z hZ
    refine (B Z).I.exists_lift_blowup ?_
    refine Scheme.IdealSheafData.IsInvertible.of_mul_left
      (K₂ := (∏ Z' ∈ s.erase Z, (B Z').I).comap I.blowupMap) ?_
    rw [← Scheme.IdealSheafData.comap_mul, Finset.mul_prod_erase s (fun Z ↦ (B Z).I) hZ, ← hIdef]
    exact I.isInvertible_comap_blowupMap
  choose cm hcm using hcex
  have hIU : Disjoint (U : Set X) (I.support : Set X) :=
    Set.disjoint_of_subset_left (fun x hx ↦ hUV hx) hIdisj
  have hisoU : IsIso (I.blowupMap ∣_ U) := I.isIso_blowupMap_restrict hIU
  obtain ⟨σ, hσiso, hσq⟩ : ∃ σ : U.toScheme ⟶ I.blowup,
      IsOpenImmersion σ ∧ σ ≫ I.blowupMap = U.ι := by
    refine ⟨inv (I.blowupMap ∣_ U) ≫ (I.blowupMap ⁻¹ᵁ U).ι, inferInstance, ?_⟩
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  have main : ∀ F : U.toScheme ⟶ pullback p I.blowupMap,
      F ≫ pullback.fst p I.blowupMap = f →
      F ≫ pullback.snd p I.blowupMap = σ →
      LocallyQuasiFinite (F.imageι ≫ pullback.snd p I.blowupMap) ∧
        LocallyOfFiniteType (F.imageι ≫ pullback.snd p I.blowupMap) ∧
        IsSeparated (F.imageι ≫ pullback.snd p I.blowupMap) ∧
        QuasiCompact (F.imageι ≫ pullback.snd p I.blowupMap) := by
    intro F hFfst hFsnd
    have : IsProper I.blowupMap := (⟨I, hIft, hIdisj⟩ : IsAdmissible X V).isProper_blowupMap
    have : CompactSpace I.blowup := QuasiCompact.compactSpace_of_compactSpace I.blowupMap
    have : QuasiSeparatedSpace I.blowup := quasiSeparatedSpace_of_quasiSeparated I.blowupMap
    have : CompactSpace (pullback p I.blowupMap : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd p I.blowupMap)
    have : QuasiSeparatedSpace (pullback p I.blowupMap : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd p I.blowupMap)
    have : QuasiCompact F := quasiCompact_of_compactSpace F
    have : CompactSpace F.image := QuasiCompact.compactSpace_of_compactSpace F.imageι
    have hkerrange : Set.range F.imageι = closure (Set.range F) := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact Scheme.Hom.support_ker F
    -- for each affine open of `Y`, a subset injecting into the blow-up and containing the
    -- part of the closure of the graph lying over it
    have key : ∀ Z : Y.affineOpens, ∃ T : Set (pullback p I.blowupMap : Scheme.{u}),
        Set.InjOn (pullback.snd p I.blowupMap) T ∧
        (Z ∈ s → closure (Set.range F) ∩ ((pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)) :
          Set (pullback p I.blowupMap : Scheme.{u})) ⊆ T) := by
      intro Z
      by_cases hZ : Z ∈ s
      swap
      · exact ⟨∅, Set.injOn_empty _, fun h ↦ absurd h hZ⟩
      have hcZ : cm Z hZ ≫ (B Z).I.blowupMap = I.blowupMap := hcm Z hZ
      have hcond : ((cm Z hZ ∣_ W Z) ≫ g Z ≫ (Z : Y.Opens).ι) ≫ p =
          (cm Z hZ ⁻¹ᵁ W Z).ι ≫ I.blowupMap := by
        rw [Category.assoc, Category.assoc, hg Z, ← Category.assoc, morphismRestrict_ι,
          Category.assoc, hcZ]
      set Φ : (cm Z hZ ⁻¹ᵁ W Z).toScheme ⟶ pullback p I.blowupMap :=
        pullback.lift ((cm Z hZ ∣_ W Z) ≫ g Z ≫ (Z : Y.Opens).ι) (cm Z hZ ⁻¹ᵁ W Z).ι hcond
        with hΦdef
      have hΦfst : Φ ≫ pullback.fst p I.blowupMap =
          (cm Z hZ ∣_ W Z) ≫ g Z ≫ (Z : Y.Opens).ι := pullback.lift_fst _ _ _
      have hΦsnd : Φ ≫ pullback.snd p I.blowupMap = (cm Z hZ ⁻¹ᵁ W Z).ι :=
        pullback.lift_snd _ _ _
      have hΦsndpt : ∀ z, (pullback.snd p I.blowupMap).base (Φ.base z) =
          (cm Z hZ ⁻¹ᵁ W Z).ι.base z := by
        intro z
        have h := congrArg (fun t : (cm Z hZ ⁻¹ᵁ W Z).toScheme ⟶ I.blowup ↦ t.base z) hΦsnd
        simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using h
      refine ⟨Set.range Φ, ?_, fun _ ↦ ?_⟩
      · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
        rw [hΦsndpt, hΦsndpt] at hab
        rw [(cm Z hZ ⁻¹ᵁ W Z).ι.isOpenEmbedding.injective hab]
      -- the containment
      have hclosedT : IsClosed ((pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)).ι ⁻¹'
          Set.range Φ) :=
        isClosed_preimage_range_lift_of_comp p (cm Z hZ) hcZ (g Z) (hg Z) (hcl Z) hcond
      -- the graph over `f ⁻¹ Z` factors through the section
      have hμr : Set.range ((f ⁻¹ᵁ (Z : Y.Opens)).ι ≫ σ) ⊆
          Set.range (cm Z hZ ⁻¹ᵁ W Z).ι := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨w, rfl⟩
        refine hle Z ?_
        change (B Z).I.blowupMap.base ((cm Z hZ).base _) ∈
          ((U.ι ''ᵁ f ⁻¹ᵁ (Z : Y.Opens) : X.Opens) : Set X)
        have h1 := congrArg (fun t : I.blowup ⟶ X ↦ t.base (σ.base ((f ⁻¹ᵁ (Z:Y.Opens)).ι.base w)))
          hcZ
        have h2 := congrArg (fun t : U.toScheme ⟶ X ↦ t.base ((f ⁻¹ᵁ (Z:Y.Opens)).ι.base w)) hσq
        simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h1 h2 ⊢
        rw [h1, h2, Scheme.Hom.coe_image]
        refine ⟨(f ⁻¹ᵁ (Z:Y.Opens)).ι.base w, ?_, rfl⟩
        rw [← Scheme.Opens.range_ι]
        exact Set.mem_range_self w
      set μ := IsOpenImmersion.lift (cm Z hZ ⁻¹ᵁ W Z).ι ((f ⁻¹ᵁ (Z : Y.Opens)).ι ≫ σ) hμr
        with hμdef
      have hμι : μ ≫ (cm Z hZ ⁻¹ᵁ W Z).ι = (f ⁻¹ᵁ (Z : Y.Opens)).ι ≫ σ :=
        IsOpenImmersion.lift_fac _ _ _
      have hμΦ : μ ≫ Φ = (f ⁻¹ᵁ (Z : Y.Opens)).ι ≫ F := by
        refine pullback.hom_ext ?_ ?_
        · have hmcond : (μ ≫ (cm Z hZ ∣_ W Z)) ≫ (W Z).ι ≫ (B Z).I.blowupMap =
              (f ⁻¹ᵁ (Z : Y.Opens)).ι ≫ U.ι := by
            rw [Category.assoc, ← Category.assoc (cm Z hZ ∣_ W Z), morphismRestrict_ι,
              Category.assoc, hcZ, ← Category.assoc, hμι, Category.assoc, hσq]
          have hagree := hagr Z (μ ≫ (cm Z hZ ∣_ W Z)) hmcond
          rw [Category.assoc, hΦfst, Category.assoc, hFfst, ← Category.assoc]
          exact hagree
        · rw [Category.assoc, hΦsnd, hμι, Category.assoc, hFsnd]
      have hsubT : (pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)).ι ⁻¹' Set.range F ⊆
          (pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)).ι ⁻¹' Set.range Φ := by
        rintro t ⟨u, hu⟩
        have hfu : f.base u ∈ ((Z : Y.Opens) : Set Y) := by
          have hmem : (pullback.fst p I.blowupMap).base
              ((pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)).ι.base t) ∈
              ((Z : Y.Opens) : Set Y) := by
            have h0 : (pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)).ι.base t ∈
                Set.range (pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)).ι :=
              Set.mem_range_self t
            rw [Scheme.Opens.range_ι] at h0
            exact h0
          rw [← hu] at hmem
          have h3 := congrArg (fun t : U.toScheme ⟶ Y ↦ t.base u) hFfst
          simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h3
          rwa [h3] at hmem
        have hw : u ∈ ((f ⁻¹ᵁ (Z : Y.Opens) : U.toScheme.Opens) : Set U.toScheme) := hfu
        have h4 := congrArg (fun t : (f ⁻¹ᵁ (Z:Y.Opens)).toScheme ⟶ pullback p I.blowupMap ↦
          t.base ⟨u, hw⟩) hμΦ
        simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h4
        refine ⟨μ.base ⟨u, hw⟩, ?_⟩
        rw [h4, ← hu]
        rfl
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      obtain ⟨t, rfl⟩ : ∃ t, (pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)).ι.base t = z := by
        have hzr : z ∈ Set.range (pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)).ι := by
          rw [Scheme.Opens.range_ι]
          exact hz2
        exact hzr
      have h5 := (pullback.fst p I.blowupMap ⁻¹ᵁ (Z : Y.Opens)).ι.isOpenEmbedding.isOpenMap
        |>.preimage_closure_subset_closure_preimage (s := Set.range F) hz1
      have h6 := closure_mono hsubT h5
      rw [hclosedT.closure_eq] at h6
      exact h6
    choose T hTinj hTsub using key
    refine ⟨?_, inferInstance, inferInstance, quasiCompact_of_compactSpace _⟩
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun x ↦ ?_
    have hpre : ⇑(F.imageι ≫ pullback.snd p I.blowupMap) ⁻¹' {x} =
        ⇑F.imageι ⁻¹' (closure (Set.range F) ∩ ⇑(pullback.snd p I.blowupMap) ⁻¹' {x}) := by
      rw [Set.preimage_inter, ← hkerrange, Set.preimage_range, Set.univ_inter]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    rw [hpre]
    refine Set.Finite.preimage (fun a _ b _ hab ↦ F.imageι.isEmbedding.injective hab) ?_
    refine Set.Finite.subset (Set.Finite.biUnion s.finite_toSet
      (fun Z _ ↦ (?_ : (T Z ∩ ⇑(pullback.snd p I.blowupMap) ⁻¹' {x}).Finite))) ?_
    · refine Set.Subsingleton.finite ?_
      rintro a ⟨ha1, ha2⟩ b ⟨hb1, hb2⟩
      exact hTinj Z ha1 hb1 (ha2.trans hb2.symm)
    · rintro z ⟨hz1, hz2⟩
      obtain ⟨Z, hZs, hZmem⟩ : ∃ Z ∈ s,
          (pullback.fst p I.blowupMap).base z ∈ ((Z : Y.Opens) : Set Y) := by
        have hmem := hs (Set.mem_univ ((pullback.fst p I.blowupMap).base z))
        simpa using hmem
      exact Set.mem_biUnion (Finset.mem_coe.mpr hZs) ⟨hTsub Z hZs ⟨hz1, hZmem⟩, hz2⟩
  exact ⟨⟨I, hIft, hIdisj⟩, σ, hσiso, hσq, main⟩

end AlgebraicGeometry
