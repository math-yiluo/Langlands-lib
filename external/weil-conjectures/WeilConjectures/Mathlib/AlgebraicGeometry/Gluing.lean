/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Gluing morphisms defined on a family of opens

Mathlib glues morphisms defined on the members of an open cover, with the compatibility
hypothesis stated as an equality of the two projections out of a fibre product. For a family
of opens `U : J → X.Opens` the fibre product of `U i` and `U j` over `⨆ i, U i` is the
intersection `U i ⊓ U j`, so the hypothesis takes the more elementary form of agreement on
the pairwise intersections. We record this form:

- `AlgebraicGeometry.Scheme.Opens.glueMorphisms` — the glued morphism `(⨆ i, U i) ⟶ Y`;
- `AlgebraicGeometry.Scheme.Opens.homOfLE_glueMorphisms` — it restricts to `f i` on `U i`;
- `AlgebraicGeometry.Scheme.Opens.hom_ext_iSup` — two morphisms out of `⨆ i, U i` agreeing on
  every `U i` are equal.

For a family of opens covering `X`, i.e. with `⨆ i, U i = ⊤`, we also record the corresponding
`AlgebraicGeometry.Scheme.Opens.glueMorphismsOfTop`, `Scheme.Opens.ι_glueMorphismsOfTop` and
`AlgebraicGeometry.Scheme.Opens.hom_ext_of_iSup_eq_top`, gluing to a morphism `X ⟶ Y`.

Finally, for morphisms into a scheme `Y` separated over a base `S`, agreement on the pairwise
intersections need not be assumed: by rigidity it follows from agreement on a single
scheme-theoretically dense open `D` contained in every `U i`. We record:

- `AlgebraicGeometry.Scheme.Opens.homOfLE_comp_eq_of_le_of_isSchemeTheoreticallyDominant` — the
  deduction of pairwise agreement from agreement on `D`;
- `AlgebraicGeometry.Scheme.Opens.glueMorphismsOfDominant` — the resulting glued morphism, with
  `AlgebraicGeometry.Scheme.Opens.homOfLE_glueMorphismsOfDominant` and
  `AlgebraicGeometry.Scheme.Opens.glueMorphismsOfDominant_comp` saying that it restricts to
  `g i` on `U i` and is a morphism over `S`.


-/

/-!
# Pushouts of open immersions of schemes

Two open immersions `f : U ⟶ X`, `g : U ⟶ Y` with common source form a span whose maps
are all open immersions, so Mathlib's locally directed gluing provides its colimit: the
pushout `X ⊔_U Y`, i.e. the scheme obtained by gluing `X` and `Y` along `U`. This file
records the basic geometry of this pushout:

- `AlgebraicGeometry.IsOpenImmersion.hasPushout`: the pushout exists;
- the inclusions `pushout.inl`/`pushout.inr` are open immersions and are jointly
  surjective (`AlgebraicGeometry.range_pushout_inl_union_range_pushout_inr`);
- `AlgebraicGeometry.IsOpenImmersion.isPullback_pushout`: the pushout square is also a
  pullback square, i.e. the two charts intersect in exactly the glued copy of `U`;
- `CompactSpace` transfers from the two charts to the pushout;
- `AlgebraicGeometry.IsZariskiLocalAtSource.pushout_desc`: a source-local property holds
  for `pushout.desc h k w` as soon as it holds for `h` and `k`;
- `AlgebraicGeometry.quasiSeparatedSpace_pushout`: the pushout of two quasi-separated
  schemes along a quasi-compact common open is quasi-separated;
- `AlgebraicGeometry.pushoutOpensDesc` and `AlgebraicGeometry.isIso_pushoutOpensDesc`: a scheme
  covered by two opens is the pushout of the two along their intersection;
- `AlgebraicGeometry.QuasiCompact.pushout_desc` and
  `AlgebraicGeometry.IsSeparated.pushout_desc`: quasi-compactness and (given that the
  graph `U ⟶ X ×_S Y` is a closed immersion) separatedness of the glued morphism.

These are the raw ingredients for the intermediate schemes `Wᵢ = U ⊔_{Uᵢ} Xᵢ°` of the
two-open compactification theorem (blueprint chapter "Nagata compactification",
`def:nagata-two-open-intermediate-schemes`).
-/

@[expose] public section


noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {J : Type*} {X Y : Scheme.{u}} (U : J → X.Opens)

/-- Morphisms `f i : U i ⟶ Y` that agree on the pairwise intersections `U i ⊓ U j` are
compatible in the sense of `AlgebraicGeometry.Scheme.Cover.glueMorphisms`, i.e. they agree on
the fibre products of the members of `Scheme.Opens.iSupOpenCover U`. -/
lemma Scheme.Opens.pullback_fst_comp_eq_snd_comp (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) (i j : J) :
    pullback.fst (X.homOfLE (le_iSup U i)) (X.homOfLE (le_iSup U j)) ≫ f i =
      pullback.snd _ _ ≫ f j := by
  rw [← cancel_epi (isPullback_opens_inf_le (le_iSup U i) (le_iSup U j)).isoPullback.hom,
    IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  exact hf i j

/-- Glue a family of morphisms `f i : U i ⟶ Y` that agree on the pairwise intersections
`U i ⊓ U j` into a morphism `(⨆ i, U i) ⟶ Y`. -/
noncomputable def Scheme.Opens.glueMorphisms (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) :
    (⨆ i, U i).toScheme ⟶ Y :=
  (iSupOpenCover U).glueMorphisms f (Scheme.Opens.pullback_fst_comp_eq_snd_comp U f hf)

@[reassoc (attr := simp)]
lemma Scheme.Opens.homOfLE_glueMorphisms (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) (i : J) :
    X.homOfLE (le_iSup U i) ≫ Scheme.Opens.glueMorphisms U f hf = f i :=
  (iSupOpenCover U).ι_glueMorphisms f _ i

/-- Two morphisms out of `⨆ i, U i` that agree on every `U i` are equal. -/
lemma Scheme.Opens.hom_ext_iSup (g₁ g₂ : (⨆ i, U i).toScheme ⟶ Y)
    (h : ∀ i, X.homOfLE (le_iSup U i) ≫ g₁ = X.homOfLE (le_iSup U i) ≫ g₂) : g₁ = g₂ :=
  (iSupOpenCover U).hom_ext g₁ g₂ h

/-- Glue a family of morphisms `f i : U i ⟶ Y` defined on a family of opens covering `X` and
agreeing on the pairwise intersections `U i ⊓ U j` into a morphism `X ⟶ Y`. -/
noncomputable def Scheme.Opens.glueMorphismsOfTop (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) :
    X ⟶ Y :=
  (X.isoOfEq hU ≪≫ X.topIso).inv ≫ Scheme.Opens.glueMorphisms U f hf

@[reassoc (attr := simp)]
lemma Scheme.Opens.ι_glueMorphismsOfTop (hU : ⨆ i, U i = ⊤) (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) (i : J) :
    (U i).ι ≫ Scheme.Opens.glueMorphismsOfTop U hU f hf = f i := by
  have hhom : (X.isoOfEq hU ≪≫ X.topIso).hom = (⨆ i, U i).ι := by simp
  rw [glueMorphismsOfTop, ← X.homOfLE_ι (le_iSup U i), ← hhom, Category.assoc,
    Iso.hom_inv_id_assoc, homOfLE_glueMorphisms]

/-- Two morphisms out of `X` that agree on every member of a family of opens covering `X` are
equal. -/
lemma Scheme.Opens.hom_ext_of_iSup_eq_top (hU : ⨆ i, U i = ⊤) (g₁ g₂ : X ⟶ Y)
    (h : ∀ i, (U i).ι ≫ g₁ = (U i).ι ≫ g₂) : g₁ = g₂ := by
  have hhom : (X.isoOfEq hU ≪≫ X.topIso).hom = (⨆ i, U i).ι := by simp
  rw [← cancel_epi (X.isoOfEq hU ≪≫ X.topIso).hom]
  refine hom_ext_iSup U _ _ fun i ↦ ?_
  rw [hhom, X.homOfLE_ι_assoc, X.homOfLE_ι_assoc, h]

section Dominant

variable {S : Scheme.{u}} (V : J → X.Opens) (D : X.Opens)

/-- Morphisms out of a family of opens into a scheme separated over `S`, agreeing on a common
scheme-theoretically dense open `D`, agree on the pairwise intersections. -/
lemma Scheme.Opens.homOfLE_comp_eq_of_le_of_isSchemeTheoreticallyDominant
    (hD : ∀ i, D ≤ V i) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (p : Y ⟶ S) [IsSeparated p] (q : X ⟶ S)
    (g : ∀ i, (V i).toScheme ⟶ Y) (hq : ∀ i, g i ≫ p = (V i).ι ≫ q)
    (hg : ∀ i j, X.homOfLE (hD i) ≫ g i = X.homOfLE (hD j) ≫ g j) (i j : J) :
    X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ g i =
      X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ g j := by
  have := IsSchemeTheoreticallyDominant.homOfLE (le_inf (hD i) (hD j))
  refine ext_of_isSchemeTheoreticallyDominant p ?_ (X.homOfLE (le_inf (hD i) (hD j))) ?_
  · rw [Category.assoc, Category.assoc, hq i, hq j, X.homOfLE_ι_assoc, X.homOfLE_ι_assoc]
  · rw [← Category.assoc, ← Category.assoc, X.homOfLE_homOfLE, X.homOfLE_homOfLE]
    exact hg i j

/-- Glue a family of morphisms `g i : V i ⟶ Y` into a scheme separated over `S` that agree on a
common scheme-theoretically dense open `D ≤ V i`, into a morphism `(⨆ i, V i) ⟶ Y`. -/
noncomputable def Scheme.Opens.glueMorphismsOfDominant
    (hD : ∀ i, D ≤ V i) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (p : Y ⟶ S) [IsSeparated p] (q : X ⟶ S)
    (g : ∀ i, (V i).toScheme ⟶ Y) (hq : ∀ i, g i ≫ p = (V i).ι ≫ q)
    (hg : ∀ i j, X.homOfLE (hD i) ≫ g i = X.homOfLE (hD j) ≫ g j) :
    (⨆ i, V i).toScheme ⟶ Y :=
  Scheme.Opens.glueMorphisms V g
    (homOfLE_comp_eq_of_le_of_isSchemeTheoreticallyDominant V D hD p q g hq hg)

@[reassoc (attr := simp)]
lemma Scheme.Opens.homOfLE_glueMorphismsOfDominant
    (hD : ∀ i, D ≤ V i) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (p : Y ⟶ S) [IsSeparated p] (q : X ⟶ S)
    (g : ∀ i, (V i).toScheme ⟶ Y) (hq : ∀ i, g i ≫ p = (V i).ι ≫ q)
    (hg : ∀ i j, X.homOfLE (hD i) ≫ g i = X.homOfLE (hD j) ≫ g j) (i : J) :
    X.homOfLE (le_iSup V i) ≫ glueMorphismsOfDominant V D hD p q g hq hg = g i :=
  homOfLE_glueMorphisms V g _ i

/-- The morphism glued from a family of `S`-morphisms is a morphism over `S`. -/
lemma Scheme.Opens.glueMorphismsOfDominant_comp
    (hD : ∀ i, D ≤ V i) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (p : Y ⟶ S) [IsSeparated p] (q : X ⟶ S)
    (g : ∀ i, (V i).toScheme ⟶ Y) (hq : ∀ i, g i ≫ p = (V i).ι ≫ q)
    (hg : ∀ i j, X.homOfLE (hD i) ≫ g i = X.homOfLE (hD j) ≫ g j) :
    glueMorphismsOfDominant V D hD p q g hq hg ≫ p = (⨆ i, V i).ι ≫ q := by
  refine hom_ext_iSup V _ _ fun i ↦ ?_
  rw [homOfLE_glueMorphismsOfDominant_assoc, hq i, X.homOfLE_ι_assoc]

end Dominant

variable {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]

/-- Every arrow of the span of two open immersions is an open immersion: the two
non-identity arrows are `f` and `g` themselves. This is what makes the span a locally
directed diagram, hence gluable. -/
instance IsOpenImmersion.span_map : ∀ {i j : WalkingSpan} (h : i ⟶ j),
    IsOpenImmersion ((span f g).map h)
  | _, _, .id _ => by rw [span_map_id]; infer_instance
  | _, _, .init WalkingPair.left => inferInstanceAs (IsOpenImmersion f)
  | _, _, .init WalkingPair.right => inferInstanceAs (IsOpenImmersion g)

/-- The pushout of two open immersions of schemes with common source exists: the span
is a locally directed diagram of open immersions, glued by
`AlgebraicGeometry.Scheme.IsLocallyDirected`. -/
instance IsOpenImmersion.hasPushout : HasPushout f g :=
  inferInstanceAs (HasColimit (span f g))

instance : IsOpenImmersion (pushout.inl f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.left))

instance : IsOpenImmersion (pushout.inr f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.right))

/-- The two charts of the pushout of two open immersions cover the pushout. -/
lemma range_pushout_inl_union_range_pushout_inr :
    Set.range (pushout.inl f g) ∪ Set.range (pushout.inr f g) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨i, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) x
  match i, y with
  | .left, y => exact Or.inl ⟨y, rfl⟩
  | .right, y => exact Or.inr ⟨y, rfl⟩
  | .zero, y =>
    refine Or.inl ⟨f y, ?_⟩
    calc pushout.inl f g (f y)
        = ((span f g).map WalkingSpan.Hom.fst ≫ colimit.ι (span f g) WalkingSpan.left) y :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = colimit.ι (span f g) WalkingSpan.zero y := by
          rw [colimit.w (span f g) WalkingSpan.Hom.fst]

/-- **The pushout square of two open immersions of schemes is also a pullback square**:
the two charts of the glued scheme intersect in exactly the glued copy of the common
source. -/
theorem IsOpenImmersion.isPullback_pushout :
    IsPullback f g (pushout.inl f g) (pushout.inr f g) := by
  have hrange : ∀ (T : Scheme.{u}) (s₁ : T ⟶ X) (s₂ : T ⟶ Y),
      s₁ ≫ pushout.inl f g = s₂ ≫ pushout.inr f g →
      ∀ t : T, ∃ u : U, f u = s₁ t ∧ g u = s₂ t := by
    intro T s₁ s₂ hs t
    have ht : colimit.ι (span f g) WalkingSpan.left (s₁ t) =
        colimit.ι (span f g) WalkingSpan.right (s₂ t) := by
      calc colimit.ι (span f g) WalkingSpan.left (s₁ t)
          = (s₁ ≫ pushout.inl f g) t := (Scheme.Hom.comp_apply _ _ _).symm
        _ = (s₂ ≫ pushout.inr f g) t := by rw [hs]
        _ = colimit.ι (span f g) WalkingSpan.right (s₂ t) := Scheme.Hom.comp_apply _ _ _
    obtain ⟨k, fi, fj, u, hu₁, hu₂⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g)).mp ht
    cases fi with
    | id => exact nomatch fj
    | init j => cases fj with
      | init j' => exact ⟨u, hu₁, hu₂⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk pushout.condition
    (fun s ↦ IsOpenImmersion.lift f s.fst ?_) (fun s ↦ IsOpenImmersion.lift_fac _ _ _)
    (fun s ↦ ?_) (fun s m hm₁ _ ↦ ?_))
  · rintro - ⟨t, rfl⟩
    obtain ⟨u, hu, -⟩ := hrange s.pt s.fst s.snd s.condition t
    exact ⟨u, hu⟩
  · rw [← cancel_mono (pushout.inr f g), Category.assoc, ← pushout.condition,
      IsOpenImmersion.lift_fac_assoc]
    exact s.condition
  · rw [← cancel_mono f, hm₁, IsOpenImmersion.lift_fac]

instance [CompactSpace X] [CompactSpace Y] : CompactSpace ↑(pushout f g) := by
  constructor
  rw [← range_pushout_inl_union_range_pushout_inr f g]
  exact (isCompact_range (pushout.inl f g).continuous).union
    (isCompact_range (pushout.inr f g).continuous)

/-- The two charts `X` and `Y` as an open cover of the pushout `X ⊔_U Y`. -/
@[simps! I₀ X f]
def IsOpenImmersion.pushoutCover : (pushout f g).OpenCover :=
  Scheme.Cover.mkOfCovers WalkingPair (fun j ↦ WalkingPair.casesOn j X Y)
    (fun j ↦ WalkingPair.casesOn j (pushout.inl f g) (pushout.inr f g))
    (fun x ↦ by
      have hx : x ∈ Set.range (pushout.inl f g) ∪ Set.range (pushout.inr f g) := by
        rw [range_pushout_inl_union_range_pushout_inr f g]
        trivial
      obtain ⟨y, hy⟩ | ⟨y, hy⟩ := hx
      exacts [⟨WalkingPair.left, y, hy⟩, ⟨WalkingPair.right, y, hy⟩])
    (fun j ↦ by cases j <;> infer_instance)

/-- **Source-local properties descend to a pushout of open immersions**: if `P` is
Zariski-local on the source and holds for `h : X ⟶ S` and `k : Y ⟶ S`, then it holds
for the glued morphism `pushout.desc h k w : X ⊔_U Y ⟶ S`. -/
lemma IsZariskiLocalAtSource.pushout_desc {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] {S : Scheme.{u}} {h : X ⟶ S} {k : Y ⟶ S}
    (w : f ≫ h = g ≫ k) (hh : P h) (hk : P k) : P (pushout.desc h k w) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (IsOpenImmersion.pushoutCover f g)]
  intro i
  cases i with
  | left => simpa only [IsOpenImmersion.pushoutCover_f, pushout.inl_desc] using hh
  | right => simpa only [IsOpenImmersion.pushoutCover_f, pushout.inr_desc] using hk

/-- **Quasi-compactness of a gluing of two schemes along a common open**: the inverse
image of a quasi-compact open under the glued morphism is the union of the images of the
two inverse images under `h` and `k`, hence quasi-compact. (Quasi-compactness of morphisms
is not Zariski-local on the source, so this does not follow from
`AlgebraicGeometry.IsZariskiLocalAtSource.pushout_desc`; what makes it work is that the
cover of the pushout has only two members.) -/
theorem QuasiCompact.pushout_desc {S : Scheme.{u}} {h : X ⟶ S} {k : Y ⟶ S}
    (w : f ≫ h = g ≫ k) [QuasiCompact h] [QuasiCompact k] :
    QuasiCompact (pushout.desc h k w) := by
  constructor
  intro V hVopen hVcompact
  have hl : IsCompact (⇑h ⁻¹' V) := QuasiCompact.isCompact_preimage _ hVopen hVcompact
  have hr : IsCompact (⇑k ⁻¹' V) := QuasiCompact.isCompact_preimage _ hVopen hVcompact
  have hcov : ⇑(pushout.desc h k w) ⁻¹' V =
      ⇑(pushout.inl f g) '' (⇑h ⁻¹' V) ∪ ⇑(pushout.inr f g) '' (⇑k ⁻¹' V) := by
    apply subset_antisymm
    · intro p hp
      have hmem : p ∈ Set.range ⇑(pushout.inl f g) ∪ Set.range ⇑(pushout.inr f g) := by
        rw [range_pushout_inl_union_range_pushout_inr f g]
        trivial
      rcases hmem with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · refine Or.inl ⟨t, ?_, rfl⟩
        rwa [Set.mem_preimage, ← pushout.inl_desc (f := f) (g := g) h k w,
          Scheme.Hom.comp_apply]
      · refine Or.inr ⟨t, ?_, rfl⟩
        rwa [Set.mem_preimage, ← pushout.inr_desc (f := f) (g := g) h k w,
          Scheme.Hom.comp_apply]
    · rintro - (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, pushout.inl_desc]
        exact ht
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, pushout.inr_desc]
        exact ht
  rw [hcov]
  exact (hl.image (pushout.inl f g).continuous).union (hr.image (pushout.inr f g).continuous)

/-- **Separatedness of a gluing of two schemes along a common open**: let `h : X ⟶ S`
and `k : Y ⟶ S` be separated morphisms restricting to the same morphism on a common
open subscheme `U`, and assume the graph morphism `(f, g) : U ⟶ X ×_S Y` is a closed
immersion. Then the glued morphism `X ⊔_U Y ⟶ S` is separated. This is the form of the
two-open criterion (Stacks Project Tag 0F3U, `IsSeparated.of_two_open_cover`) used for
the intermediate schemes of the two-open compactification theorem. -/
theorem IsSeparated.pushout_desc {S : Scheme.{u}} {h : X ⟶ S} {k : Y ⟶ S}
    (w : f ≫ h = g ≫ k) [IsSeparated h] [IsSeparated k]
    (hd : IsClosedImmersion (pullback.lift f g w)) :
    IsSeparated (pushout.desc h k w) := by
  have h₁ : IsSeparated (pushout.inl f g ≫ pushout.desc h k w) := by
    rw [pushout.inl_desc]
    infer_instance
  have h₂ : IsSeparated (pushout.inr f g ≫ pushout.desc h k w) := by
    rw [pushout.inr_desc]
    infer_instance
  refine IsSeparated.of_two_open_cover (pushout.desc h k w) (pushout.inl f g)
    (pushout.inr f g) (range_pushout_inl_union_range_pushout_inr f g) ?_
  have hp := IsOpenImmersion.isPullback_pushout f g
  have heq : pullback.map (pushout.inl f g) (pushout.inr f g)
      (pushout.inl f g ≫ pushout.desc h k w) (pushout.inr f g ≫ pushout.desc h k w)
      (𝟙 X) (𝟙 Y) (pushout.desc h k w) (by simp) (by simp) =
      hp.isoPullback.inv ≫ pullback.lift f g w ≫
        (pullback.congrHom (pushout.inl_desc h k w) (pushout.inr_desc h k w)).inv := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.congrHom_inv, pullback.lift_fst,
        Category.comp_id, hp.isoPullback_inv_fst]
    · simp only [Category.assoc, pullback.congrHom_inv, pullback.lift_snd,
        Category.comp_id, hp.isoPullback_inv_snd]
  rw [heq]
  have := hd
  infer_instance


section PointsAndMap

/-!
### Points of the pushout, and morphisms of pushouts

The point-level description of the glued scheme: `inl x = inr y` if and only if `x` and
`y` have a common preimage in `U`. From this we deduce that the preimage of one chart
under the other chart's inclusion is exactly the image of `U`, and that for a morphism
of spans of open immersions with one cartesian component square, the corresponding
component square of the induced morphism of pushouts is cartesian as well.
-/

lemma pushout_inl_eq_inr_iff (x : X) (y : Y) :
    pushout.inl f g x = pushout.inr f g y ↔ ∃ u : U, f u = x ∧ g u = y := by
  rw [show pushout.inl f g x = pushout.inr f g y ↔
      colimit.ι (span f g) WalkingSpan.left x = colimit.ι (span f g) WalkingSpan.right y from
    Iff.rfl, Scheme.IsLocallyDirected.ι_eq_ι_iff]
  constructor
  · rintro ⟨k, fi, fj, u, hx, hy⟩
    obtain (_ | ⟨_ | _⟩) := k
    · rw [Subsingleton.elim fi WalkingSpan.Hom.fst] at hx
      rw [Subsingleton.elim fj WalkingSpan.Hom.snd] at hy
      exact ⟨u, hx, hy⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨u, hx, hy⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, u, hx, hy⟩

lemma opensRange_pushout_inl_sup_opensRange_pushout_inr :
    (pushout.inl f g).opensRange ⊔ (pushout.inr f g).opensRange = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [TopologicalSpace.Opens.mem_sup]
  exact Set.eq_univ_iff_forall.mp (range_pushout_inl_union_range_pushout_inr f g) x

lemma preimage_opensRange_pushout_inl :
    pushout.inr f g ⁻¹ᵁ (pushout.inl f g).opensRange = g.opensRange := by
  ext z
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨u, -, rfl⟩ := (pushout_inl_eq_inr_iff f g y z).mp hy
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨f u, (pushout_inl_eq_inr_iff f g _ _).mpr ⟨u, rfl, rfl⟩⟩

lemma preimage_opensRange_pushout_inr :
    pushout.inl f g ⁻¹ᵁ (pushout.inr f g).opensRange = f.opensRange := by
  ext y
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨u, rfl, -⟩ := (pushout_inl_eq_inr_iff f g y z).mp hz.symm
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨g u, ((pushout_inl_eq_inr_iff f g _ _).mpr ⟨u, rfl, rfl⟩).symm⟩

variable {U' X' Y' : Scheme.{u}} (f' : U' ⟶ X') (g' : U' ⟶ Y')
  [IsOpenImmersion f'] [IsOpenImmersion g']
  (α : X' ⟶ X) (β : Y' ⟶ Y) (γ : U' ⟶ U)
  (hf : γ ≫ f = f' ≫ α) (hg : γ ≫ g = g' ≫ β)

include hf hg in
lemma preimage_opensRange_pushout_inl_of_isPullback (H : IsPullback γ g' g β) :
    pushout.map f' g' f g α β γ hf.symm hg.symm ⁻¹ᵁ (pushout.inl f g).opensRange =
      (pushout.inl f' g').opensRange := by
  apply le_antisymm
  · rintro p hp
    have : p ∈ (pushout.inl f' g').opensRange ⊔ (pushout.inr f' g').opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (hmem | ⟨z', rfl⟩) := this
    · exact hmem
    · replace hp : (pushout.inr f' g' ≫ pushout.map f' g' f g α β γ hf.symm hg.symm) z' ∈
          (pushout.inl f g).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inr_desc] at hp
      obtain ⟨y, hy⟩ := hp
      obtain ⟨u, -, hu⟩ := (pushout_inl_eq_inr_iff f g y (β z')).mp
        (by rwa [Scheme.Hom.comp_apply] at hy)
      obtain ⟨u', -, rfl⟩ := Scheme.exists_preimage_of_isPullback H u z' hu
      change pushout.inr f' g' (g' u') ∈ (pushout.inl f' g').opensRange
      exact ⟨f' u', (pushout_inl_eq_inr_iff f' g' _ _).mpr ⟨u', rfl, rfl⟩⟩
  · rintro p ⟨y', rfl⟩
    change (pushout.inl f' g' ≫ pushout.map f' g' f g α β γ hf.symm hg.symm) y' ∈
      (pushout.inl f g).opensRange
    rw [pushout.inl_desc, Scheme.Hom.comp_apply]
    exact ⟨α y', rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `Y`-component square is cartesian,
the `X`-component square of the induced morphism of pushouts is cartesian. -/
lemma isPullback_pushout_map_inl_of_isPullback (H : IsPullback γ g' g β) :
    IsPullback α (pushout.inl f' g') (pushout.inl f g)
      (pushout.map f' g' f g α β γ hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inl_desc _ _ _)
    (preimage_opensRange_pushout_inl_of_isPullback f g f' g' α β γ hf hg H)

include hf hg in
lemma preimage_opensRange_pushout_inr_of_isPullback (H : IsPullback γ f' f α) :
    pushout.map f' g' f g α β γ hf.symm hg.symm ⁻¹ᵁ (pushout.inr f g).opensRange =
      (pushout.inr f' g').opensRange := by
  apply le_antisymm
  · rintro p hp
    have : p ∈ (pushout.inl f' g').opensRange ⊔ (pushout.inr f' g').opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (⟨y', rfl⟩ | hmem) := this
    · replace hp : (pushout.inl f' g' ≫ pushout.map f' g' f g α β γ hf.symm hg.symm) y' ∈
          (pushout.inr f g).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inl_desc] at hp
      obtain ⟨z, hz⟩ := hp
      obtain ⟨u, hu, -⟩ := (pushout_inl_eq_inr_iff f g (α y') z).mp
        (by rw [Scheme.Hom.comp_apply] at hz; exact hz.symm)
      obtain ⟨u', -, rfl⟩ := Scheme.exists_preimage_of_isPullback H u y' hu
      change pushout.inl f' g' (f' u') ∈ (pushout.inr f' g').opensRange
      exact ⟨g' u', ((pushout_inl_eq_inr_iff f' g' _ _).mpr ⟨u', rfl, rfl⟩).symm⟩
    · exact hmem
  · rintro p ⟨z', rfl⟩
    change (pushout.inr f' g' ≫ pushout.map f' g' f g α β γ hf.symm hg.symm) z' ∈
      (pushout.inr f g).opensRange
    rw [pushout.inr_desc, Scheme.Hom.comp_apply]
    exact ⟨β z', rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `X`-component square is cartesian,
the `Y`-component square of the induced morphism of pushouts is cartesian. -/
lemma isPullback_pushout_map_inr_of_isPullback (H : IsPullback γ f' f α) :
    IsPullback β (pushout.inr f' g') (pushout.inr f g)
      (pushout.map f' g' f g α β γ hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inr_desc _ _ _)
    (preimage_opensRange_pushout_inr_of_isPullback f g f' g' α β γ hf hg H)

end PointsAndMap

section QuasiSeparated

lemma image_inl_inter_image_inr (A : Set X) (B : Set Y) :
    (pushout.inl f g '' A) ∩ (pushout.inr f g '' B) = pushout.inl f g '' (A ∩ f '' (g ⁻¹' B)) := by
  apply subset_antisymm
  · rintro - ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    obtain ⟨u, hu, rfl⟩ := (pushout_inl_eq_inr_iff f g x y).mp hxy.symm
    exact ⟨x, ⟨hx, ⟨u, hy, hu⟩⟩, rfl⟩
  · rintro - ⟨x, ⟨hx, ⟨u, hu, rfl⟩⟩, rfl⟩
    exact ⟨⟨f u, hx, rfl⟩, ⟨g u, hu, ((pushout_inl_eq_inr_iff f g _ _).mpr ⟨u, rfl, rfl⟩).symm⟩⟩

/-- **The pushout of two quasi-separated schemes along a quasi-compact common open is
quasi-separated.** -/
lemma quasiSeparatedSpace_pushout [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
    [CompactSpace U] : QuasiSeparatedSpace ↑(pushout f g) := by
  have hgc : IsCompact (Set.range g) := isCompact_range g.continuous
  -- the intersection of a compact open of `X` with a compact open of `Y` inside the pushout
  have key : ∀ (A : Set X) (B : Set Y), IsOpen A → IsCompact A → IsOpen B → IsCompact B →
      IsCompact ((pushout.inl f g '' A) ∩ (pushout.inr f g '' B)) := by
    intro A B hAo hAc hBo hBc
    rw [image_inl_inter_image_inr]
    refine IsCompact.image ?_ (pushout.inl f g).continuous
    have h₁ : IsCompact (g ⁻¹' B) := by
      have he : g ⁻¹' B = g ⁻¹' (B ∩ Set.range g) := by
        rw [Set.preimage_inter, Set.preimage_range, Set.inter_univ]
      rw [he]
      exact g.isOpenEmbedding.isInducing.isCompact_preimage'
        (hBc.inter_of_isOpen hgc hBo g.isOpenEmbedding.isOpen_range) Set.inter_subset_right
    exact hAc.inter_of_isOpen (h₁.image f.continuous) hAo
      (f.isOpenEmbedding.isOpenMap _ (hBo.preimage g.continuous))
  refine QuasiSeparatedSpace.of_isTopologicalBasis
    (b := fun i : {A : X.Opens // IsCompact (A : Set X)} ⊕ {B : Y.Opens // IsCompact (B : Set Y)} ↦
      match i with
      | Sum.inl A => pushout.inl f g '' (A.1 : Set X)
      | Sum.inr B => pushout.inr f g '' (B.1 : Set Y))
    ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro - ⟨(⟨A, hA⟩ | ⟨B, hB⟩), rfl⟩
      · exact (pushout.inl f g).isOpenEmbedding.isOpenMap _ A.2
      · exact (pushout.inr f g).isOpenEmbedding.isOpenMap _ B.2
    · intro p O hp hO
      have hcov : p ∈ Set.range (pushout.inl f g) ∪ Set.range (pushout.inr f g) := by
        rw [range_pushout_inl_union_range_pushout_inr f g]; trivial
      obtain (⟨x, rfl⟩ | ⟨y, rfl⟩) := hcov
      · have hmem : x ∈ (⟨_, hO.preimage (pushout.inl f g).continuous⟩ : X.Opens) := hp
        obtain ⟨A₀, hA₀, hxA, hAO⟩ :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hmem
        exact ⟨_, ⟨Sum.inl ⟨A₀, hA₀.isCompact⟩, rfl⟩, ⟨x, hxA, rfl⟩,
          Set.image_subset_iff.mpr hAO⟩
      · have hmem : y ∈ (⟨_, hO.preimage (pushout.inr f g).continuous⟩ : Y.Opens) := hp
        obtain ⟨B₀, hB₀, hyB, hBO⟩ :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hmem
        exact ⟨_, ⟨Sum.inr ⟨B₀, hB₀.isCompact⟩, rfl⟩, ⟨y, hyB, rfl⟩,
          Set.image_subset_iff.mpr hBO⟩
  · rintro (⟨A, hA⟩ | ⟨B, hB⟩) (⟨A', hA'⟩ | ⟨B', hB'⟩)
    · rw [← Set.image_inter (pushout.inl f g).isOpenEmbedding.injective]
      exact (hA.inter_of_isOpen hA' A.2 A'.2).image (pushout.inl f g).continuous
    · exact key _ _ A.2 hA B'.2 hB'
    · rw [Set.inter_comm]
      exact key _ _ A'.2 hA' B.2 hB
    · rw [← Set.image_inter (pushout.inr f g).isOpenEmbedding.injective]
      exact (hB.inter_of_isOpen hB' B.2 B'.2).image (pushout.inr f g).continuous

end QuasiSeparated

section TwoOpens

variable {Z : Scheme.{u}} (U V : Z.Opens)

/-- (Implementation) The inclusion of the intersection of two opens into the first one. -/
abbrev Scheme.Opens.infHomLeft : (U ⊓ V : Z.Opens).toScheme ⟶ U.toScheme :=
  Z.homOfLE inf_le_left

/-- (Implementation) The inclusion of the intersection of two opens into the second one. -/
abbrev Scheme.Opens.infHomRight : (U ⊓ V : Z.Opens).toScheme ⟶ V.toScheme :=
  Z.homOfLE inf_le_right

/-- The morphism from the pushout of two opens of `Z` along their intersection to `Z`. -/
def pushoutOpensDesc :
    pushout (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V) ⟶ Z :=
  pushout.desc U.ι V.ι (by simp)

@[reassoc (attr := simp)]
lemma inl_pushoutOpensDesc :
    pushout.inl (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V) ≫
      pushoutOpensDesc U V = U.ι :=
  pushout.inl_desc ..

@[reassoc (attr := simp)]
lemma inr_pushoutOpensDesc :
    pushout.inr (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V) ≫
      pushoutOpensDesc U V = V.ι :=
  pushout.inr_desc ..

lemma preimage_opensRange_inl_pushoutOpensDesc :
    pushoutOpensDesc U V ⁻¹ᵁ U.ι.opensRange =
      (pushout.inl (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)).opensRange := by
  apply le_antisymm
  · intro x hx
    have hcov : x ∈ (pushout.inl (Scheme.Opens.infHomLeft U V)
        (Scheme.Opens.infHomRight U V)).opensRange ⊔
        (pushout.inr (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)).opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (hmem | ⟨v, rfl⟩) := hcov
    · exact hmem
    · replace hx : (pushout.inr (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V) ≫
          pushoutOpensDesc U V) v ∈ U.ι.opensRange := hx
      rw [inr_pushoutOpensDesc] at hx
      obtain ⟨u, hu⟩ := hx
      change v ∈ pushout.inr (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V) ⁻¹ᵁ
        (pushout.inl (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)).opensRange
      rw [preimage_opensRange_pushout_inl, Scheme.opensRange_homOfLE]
      exact ⟨show V.ι v ∈ U from hu ▸ u.2, v.2⟩
  · rintro x ⟨u, rfl⟩
    change (pushout.inl (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V) ≫
      pushoutOpensDesc U V) u ∈ U.ι.opensRange
    rw [inl_pushoutOpensDesc]
    exact ⟨u, rfl⟩

lemma preimage_opensRange_inr_pushoutOpensDesc :
    pushoutOpensDesc U V ⁻¹ᵁ V.ι.opensRange =
      (pushout.inr (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)).opensRange := by
  apply le_antisymm
  · intro x hx
    have hcov : x ∈ (pushout.inl (Scheme.Opens.infHomLeft U V)
        (Scheme.Opens.infHomRight U V)).opensRange ⊔
        (pushout.inr (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)).opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (⟨u, rfl⟩ | hmem) := hcov
    · replace hx : (pushout.inl (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V) ≫
          pushoutOpensDesc U V) u ∈ V.ι.opensRange := hx
      rw [inl_pushoutOpensDesc] at hx
      obtain ⟨v, hv⟩ := hx
      change u ∈ pushout.inl (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V) ⁻¹ᵁ
        (pushout.inr (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)).opensRange
      rw [preimage_opensRange_pushout_inr, Scheme.opensRange_homOfLE]
      exact ⟨u.2, show U.ι u ∈ V from hv ▸ v.2⟩
    · exact hmem
  · rintro x ⟨v, rfl⟩
    change (pushout.inr (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V) ≫
      pushoutOpensDesc U V) v ∈ V.ι.opensRange
    rw [inr_pushoutOpensDesc]
    exact ⟨v, rfl⟩

/-- The first chart of the pushout presentation of a two-open cover is cartesian. -/
lemma isPullback_inl_pushoutOpensDesc :
    IsPullback (𝟙 U.toScheme)
      (pushout.inl (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)) U.ι
      (pushoutOpensDesc U V) :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp) (preimage_opensRange_inl_pushoutOpensDesc U V)

/-- The second chart of the pushout presentation of a two-open cover is cartesian. -/
lemma isPullback_inr_pushoutOpensDesc :
    IsPullback (𝟙 V.toScheme)
      (pushout.inr (Scheme.Opens.infHomLeft U V) (Scheme.Opens.infHomRight U V)) V.ι
      (pushoutOpensDesc U V) :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp) (preimage_opensRange_inr_pushoutOpensDesc U V)

/-- **A scheme covered by two open subschemes is the pushout of the two along their
intersection.** -/
lemma isIso_pushoutOpensDesc (hUV : U ⊔ V = ⊤) : IsIso (pushoutOpensDesc U V) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover
    (Z.openCoverOfIsOpenCover (fun b : Bool ↦ cond b U V) ?_) fun b ↦ ?_
  · change iSup _ = ⊤
    rw [iSup_bool_eq]
    exact hUV
  · rw [MorphismProperty.isomorphisms.iff]
    match b with
    | true =>
      change IsIso (pullback.snd (pushoutOpensDesc U V) U.ι)
      have h := (isPullback_inl_pushoutOpensDesc U V).flip
      have e : pullback.snd (pushoutOpensDesc U V) U.ι = h.isoPullback.inv := by
        rw [← Category.id_comp (pullback.snd (pushoutOpensDesc U V) U.ι),
          ← h.isoPullback.inv_hom_id, Category.assoc, IsPullback.isoPullback_hom_snd,
          Category.comp_id]
      rw [e]; infer_instance
    | false =>
      change IsIso (pullback.snd (pushoutOpensDesc U V) V.ι)
      have h := (isPullback_inr_pushoutOpensDesc U V).flip
      have e : pullback.snd (pushoutOpensDesc U V) V.ι = h.isoPullback.inv := by
        rw [← Category.id_comp (pullback.snd (pushoutOpensDesc U V) V.ι),
          ← h.isoPullback.inv_hom_id, Category.assoc, IsPullback.isoPullback_hom_snd,
          Category.comp_id]
      rw [e]; infer_instance

end TwoOpens

section ContinuousMap

variable {M : Type*} [TopologicalSpace M] [DiscreteTopology M] {X Y : Scheme.{u}}

/-- The open subscheme `f⁻¹(m)` of a scheme `X`, for a continuous map `f : X → M` to a
discrete space. -/
def Scheme.fiberOpens (f : C(X, M)) (m : M) : X.Opens :=
  ⟨f ⁻¹' {m}, (isOpen_discrete _).preimage f.continuous⟩

@[simp]
lemma Scheme.mem_fiberOpens (f : C(X, M)) (m : M) (x : X) : x ∈ X.fiberOpens f m ↔ f x = m :=
  Iff.rfl

lemma Scheme.iSup_fiberOpens (f : C(X, M)) : ⨆ m, X.fiberOpens f m = ⊤ :=
  eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨f x, rfl⟩

/-- Two morphisms out of `X` are equal if they agree on every fibre of a continuous map
`f : X → M` to a discrete space. -/
lemma Scheme.hom_ext_fiberOpens (f : C(X, M)) {g₁ g₂ : X ⟶ Y}
    (h : ∀ m, (X.fiberOpens f m).ι ≫ g₁ = (X.fiberOpens f m).ι ≫ g₂) : g₁ = g₂ :=
  Scheme.Opens.hom_ext_of_iSup_eq_top _ (X.iSup_fiberOpens f) g₁ g₂ h

/-- Morphisms out of the intersection of two distinct fibres agree: the intersection is
empty. -/
lemma Scheme.homOfLE_fiberOpens_comp (f : C(X, M)) (g : M → (X ⟶ Y)) (m n : M) :
    X.homOfLE (inf_le_left : X.fiberOpens f m ⊓ X.fiberOpens f n ≤ _) ≫
        (X.fiberOpens f m).ι ≫ g m =
      X.homOfLE (inf_le_right : X.fiberOpens f m ⊓ X.fiberOpens f n ≤ _) ≫
        (X.fiberOpens f n).ι ≫ g n := by
  by_cases hmn : m = n
  · subst hmn
    rfl
  · have : IsEmpty (X.fiberOpens f m ⊓ X.fiberOpens f n).toScheme :=
      ⟨fun x ↦ hmn ((x.2.1 : f x.1 = m).symm.trans x.2.2)⟩
    exact isInitialOfIsEmpty.hom_ext _ _

/-- **Gluing along the fibres of a locally constant function.** For a continuous map
`f : X → M` to a discrete space and a family of morphisms `g m : X ⟶ Y`, the morphism
`X ⟶ Y` which is `g m` on the open fibre `f⁻¹(m)`. -/
noncomputable def Scheme.glueOfContinuousMap (f : C(X, M)) (g : M → (X ⟶ Y)) : X ⟶ Y :=
  Scheme.Opens.glueMorphismsOfTop (X.fiberOpens f) (X.iSup_fiberOpens f)
    (fun m ↦ (X.fiberOpens f m).ι ≫ g m) (Scheme.homOfLE_fiberOpens_comp f g)

@[reassoc (attr := simp)]
lemma Scheme.fiberOpens_ι_glueOfContinuousMap (f : C(X, M)) (g : M → (X ⟶ Y)) (m : M) :
    (X.fiberOpens f m).ι ≫ X.glueOfContinuousMap f g = (X.fiberOpens f m).ι ≫ g m :=
  Scheme.Opens.ι_glueMorphismsOfTop _ _ _ _ m

lemma Scheme.glueOfContinuousMap_comp {Z : Scheme.{u}} (f : C(X, M)) (g : M → (X ⟶ Y))
    (h : Y ⟶ Z) : X.glueOfContinuousMap f g ≫ h = X.glueOfContinuousMap f (fun m ↦ g m ≫ h) :=
  X.hom_ext_fiberOpens f fun m ↦ by simp

lemma Scheme.glueOfContinuousMap_eq {f : C(X, M)} {g : M → (X ⟶ Y)} {g' : X ⟶ Y}
    (h : ∀ m, (X.fiberOpens f m).ι ≫ g m = (X.fiberOpens f m).ι ≫ g') :
    X.glueOfContinuousMap f g = g' :=
  X.hom_ext_fiberOpens f fun m ↦ by simp [h]

/-- Gluing is compatible with precomposition: `φ ≫ glue f g` is glued from the `φ ≫ g m` along
the fibres of `f ∘ φ`. -/
lemma Scheme.comp_glueOfContinuousMap {X' : Scheme.{u}} (φ : X' ⟶ X) (f : C(X, M))
    (g : M → (X ⟶ Y)) :
    φ ≫ X.glueOfContinuousMap f g =
      X'.glueOfContinuousMap (f.comp φ.base.hom) (fun m ↦ φ ≫ g m) := by
  refine X'.hom_ext_fiberOpens (f.comp φ.base.hom) fun m ↦ ?_
  have e : X'.fiberOpens (f.comp φ.base.hom) m = φ ⁻¹ᵁ X.fiberOpens f m := rfl
  rw [Scheme.fiberOpens_ι_glueOfContinuousMap, e, ← morphismRestrict_ι_assoc,
    Scheme.fiberOpens_ι_glueOfContinuousMap, morphismRestrict_ι_assoc]

end ContinuousMap

end AlgebraicGeometry
