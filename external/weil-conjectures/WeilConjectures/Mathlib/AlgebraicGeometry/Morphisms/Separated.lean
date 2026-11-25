/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# Complements on separated morphisms

This file collects complements on separated morphisms of schemes.

## The diagonal of a separated morphism locally of finite presentation

For a separated morphism the diagonal is a closed immersion. Combined with
`AlgebraicGeometry.locallyOfFinitePresentation_diagonal` this shows that the diagonal of a
separated morphism locally of finite presentation is a closed immersion of finite presentation
(`AlgebraicGeometry.Scheme.Hom.diagonal_isClosedImmersion_finitePresentation`).

## Separatedness from an open cover of the source

We prove the criterion of separatedness over an open cover (Stacks Project Tag 0F3U):
`w : W ⟶ S` is separated as soon as `W` has an open cover `𝒰` for which every overlap
morphism `𝒰ᵢ ×_W 𝒰ⱼ ⟶ 𝒰ᵢ ×_S 𝒰ⱼ` is a closed immersion
(`AlgebraicGeometry.IsSeparated.of_openCover`), together with its two-element special
case `AlgebraicGeometry.IsSeparated.of_two_open_cover`, in which the diagonal overlaps
are supplied by separatedness of `T₁ ⟶ S` and `T₂ ⟶ S`.

The proof covers `W ×_S W` by the chart opens `𝒰ᵢ ×_S 𝒰ⱼ` and identifies the
restriction of the diagonal over such a chart with the overlap morphism
(`AlgebraicGeometry.diagonalRestrictChartArrowIso`); over the diagonal charts that
morphism is the closed-immersion diagonal of `𝒰ᵢ ⟶ S`
(`AlgebraicGeometry.isClosedImmersion_pullback_map_self`), and the two mixed charts of
a two-element cover are exchanged by the symmetry isomorphism
(`AlgebraicGeometry.pullback_map_symmetry`).

## The affine criterion for separatedness

`AlgebraicGeometry.IsSeparatingPair X U V` says that `Γ(X, U ⊓ V)` is generated as a ring by
the images of the restriction maps from `Γ(X, U)` and `Γ(X, V)`. For affine `U`, `V` and `U ⊓ V`
this is equivalent to `U ⊓ V ⟶ U × V` being a closed immersion
(`AlgebraicGeometry.isSeparatingPair_iff`), which gives the classical criterion: a scheme all of
whose affine opens in some cover pairwise satisfy it (with affine intersections) is separated
(`AlgebraicGeometry.Scheme.isSeparated_of_isSeparatingPair`), and conversely
(`AlgebraicGeometry.isSeparatingPair_of_isSeparated`).

## Morphisms agreeing on a scheme-theoretically dominant subscheme

Two morphisms into a separated target that agree after precomposition with a
scheme-theoretically dominant morphism are equal
(`AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant_of_isSeparated` and its
version for morphisms over a base
`AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant_of_isSeparated'`). This is
the scheme-theoretic analogue of Mathlib's
`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`, with the reducedness assumption
on the source dropped.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Diagonal

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The diagonal of a separated morphism of finite presentation is a closed immersion of
finite presentation.**

Mathlib has no bundled class for "of finite presentation"; a morphism is of finite presentation
if it is locally of finite presentation, quasi-compact and quasi-separated. -/
theorem Scheme.Hom.diagonal_isClosedImmersion_finitePresentation [IsSeparated f]
    [LocallyOfFinitePresentation f] :
    IsClosedImmersion (pullback.diagonal f) ∧
      LocallyOfFinitePresentation (pullback.diagonal f) ∧
      QuasiCompact (pullback.diagonal f) ∧ QuasiSeparated (pullback.diagonal f) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩


end Diagonal

variable {W S : Scheme.{u}} (w : W ⟶ S)

section TwoOpenCover

variable {T₁ T₂ : Scheme.{u}} (j₁ : T₁ ⟶ W) (j₂ : T₂ ⟶ W)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂]

/-- The restriction of the diagonal of `w : W ⟶ S` over the chart
`T₁ ×_S T₂ ⊆ W ×_S W` attached to a pair of open immersions `jᵢ : Tᵢ ⟶ W` is the
canonical morphism `T₁ ×_W T₂ ⟶ T₁ ×_S T₂`. -/
def diagonalRestrictChartArrowIso :
    Arrow.mk (pullback.diagonal w ∣_
        (pullback.map (j₁ ≫ w) (j₂ ≫ w) w w j₁ j₂ (𝟙 S) (by simp) (by simp)).opensRange) ≅
      Arrow.mk (pullback.map j₁ j₂ (j₁ ≫ w) (j₂ ≫ w) (𝟙 T₁) (𝟙 T₂) w
        (by simp) (by simp)) := by
  refine morphismRestrictArrowIso (pullback.diagonal w)
    (e := pullback.fst j₁ j₂ ≫ j₁) _ ?_ ?_
  · apply pullback.hom_ext
    · simp
    · simp [pullback.condition]
  · have hΔfst : ∀ y : W, (pullback.fst w w) (pullback.diagonal w y) = y := fun y ↦ by
      rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
      simp
    have hΔsnd : ∀ y : W, (pullback.snd w w) (pullback.diagonal w y) = y := fun y ↦ by
      rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]
      simp
    ext x
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      Scheme.Hom.mem_opensRange]
    constructor
    · rintro ⟨t, ht⟩
      have hx : pullback.diagonal w x ∈
          Set.range (pullback.map (j₁ ≫ w) (j₂ ≫ w) w w j₁ j₂ (𝟙 S)
            (by simp) (by simp)) := ⟨t, ht⟩
      rw [Scheme.Pullback.range_map] at hx
      obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hx
      rw [hΔfst] at hx₁
      rw [hΔsnd] at hx₂
      have hr : x ∈ Set.range (pullback.fst j₁ j₂ ≫ j₁) := by
        rw [Scheme.Pullback.range_fst_comp]
        exact ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      exact hr
    · rintro ⟨t, ht⟩
      have hx : x ∈ Set.range (pullback.fst j₁ j₂ ≫ j₁) := ⟨t, ht⟩
      rw [Scheme.Pullback.range_fst_comp] at hx
      obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hx
      have hr : pullback.diagonal w x ∈
          Set.range (pullback.map (j₁ ≫ w) (j₂ ≫ w) w w j₁ j₂ (𝟙 S)
            (by simp) (by simp)) := by
        rw [Scheme.Pullback.range_map]
        refine ⟨⟨x₁, ?_⟩, ⟨x₂, ?_⟩⟩
        · rw [hΔfst]
          exact hx₁
        · rw [hΔsnd]
          exact hx₂
      exact hr

variable {j₁ j₂}

/-- Over a diagonal chart, the canonical morphism `T ×_W T ⟶ T ×_S T` is the diagonal
of `T ⟶ S` up to the diagonal isomorphism of the monomorphism `j : T ⟶ W`; it is a
closed immersion whenever `T ⟶ S` is separated. -/
theorem isClosedImmersion_pullback_map_self {T : Scheme.{u}} (j : T ⟶ W) [Mono j]
    [IsSeparated (j ≫ w)] :
    IsClosedImmersion (pullback.map j j (j ≫ w) (j ≫ w) (𝟙 T) (𝟙 T) w
      (by simp) (by simp)) := by
  have hdiag : pullback.map j j (j ≫ w) (j ≫ w) (𝟙 T) (𝟙 T) w (by simp) (by simp) =
      inv (pullback.diagonal j) ≫ pullback.diagonal (j ≫ w) := by
    rw [IsIso.eq_inv_comp]
    apply pullback.hom_ext <;> simp
  rw [hdiag]
  infer_instance

omit [IsOpenImmersion j₁] [IsOpenImmersion j₂] in
/-- The mixed chart morphisms `T₁ ×_W T₂ ⟶ T₁ ×_S T₂` and `T₂ ×_W T₁ ⟶ T₂ ×_S T₁` are
related by the symmetry isomorphisms of the fibre products. -/
theorem pullback_map_symmetry :
    pullback.map j₂ j₁ (j₂ ≫ w) (j₁ ≫ w) (𝟙 T₂) (𝟙 T₁) w (by simp) (by simp) =
      (pullbackSymmetry j₂ j₁).hom ≫
        pullback.map j₁ j₂ (j₁ ≫ w) (j₂ ≫ w) (𝟙 T₁) (𝟙 T₂) w (by simp) (by simp) ≫
        (pullbackSymmetry (j₁ ≫ w) (j₂ ≫ w)).hom := by
  apply pullback.hom_ext <;> simp

variable (j₁ j₂)

/-- **Separatedness is detected on an open cover of the source** (Stacks Project
Tag 0F3U): if `𝒰` is an open cover of `W` and every canonical overlap morphism
`𝒰ᵢ ×_W 𝒰ⱼ ⟶ 𝒰ᵢ ×_S 𝒰ⱼ` is a closed immersion, then `w : W ⟶ S` is separated. The
diagonal cases `i = j` say exactly that `𝒰ᵢ ⟶ S` is separated, see
`AlgebraicGeometry.isClosedImmersion_pullback_map_self`. -/
theorem IsSeparated.of_openCover (𝒰 : W.OpenCover)
    (hd : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.map (𝒰.f i) (𝒰.f j)
      (𝒰.f i ≫ w) (𝒰.f j ≫ w) (𝟙 (𝒰.X i)) (𝟙 (𝒰.X j)) w (by simp) (by simp))) :
    IsSeparated w := by
  constructor
  -- the product charts `𝒰ᵢ ×_S 𝒰ⱼ` of `W ×_S W`
  let c : 𝒰.I₀ × 𝒰.I₀ → (pullback w w).Opens := fun p ↦
    (pullback.map (𝒰.f p.1 ≫ w) (𝒰.f p.2 ≫ w) w w (𝒰.f p.1) (𝒰.f p.2) (𝟙 S)
      (by simp) (by simp)).opensRange
  have hO : (⨆ p : 𝒰.I₀ × 𝒰.I₀, c p) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨(𝒰.idx (pullback.fst w w z), 𝒰.idx (pullback.snd w w z)), ?_⟩
    simp only [c, Scheme.Hom.mem_opensRange, ← Set.mem_range, Scheme.Pullback.range_map]
    exact ⟨𝒰.covers _, 𝒰.covers _⟩
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) c hO]
  rintro ⟨i, j⟩
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (diagonalRestrictChartArrowIso w (𝒰.f i) (𝒰.f j))).mpr (hd i j)

/-- **Separatedness from a two-open cover** (Stacks Project Tag 0F3U; blueprint:
`lemma:nagata-separated-two-open-cover`): let `W = T₁ ∪ T₂` be a union of two open
subschemes over `S` such that each `Tᵢ ⟶ S` is separated and the canonical overlap
morphism `T₁ ×_W T₂ ⟶ T₁ ×_S T₂` is a closed immersion. Then `W ⟶ S` is separated.
This is the two-element case of `AlgebraicGeometry.IsSeparated.of_openCover`. -/
theorem IsSeparated.of_two_open_cover
    (hcov : Set.range j₁ ∪ Set.range j₂ = Set.univ)
    [IsSeparated (j₁ ≫ w)] [IsSeparated (j₂ ≫ w)]
    (hd : IsClosedImmersion (pullback.map j₁ j₂ (j₁ ≫ w) (j₂ ≫ w) (𝟙 T₁) (𝟙 T₂) w
      (by simp) (by simp))) :
    IsSeparated w := by
  -- the remaining mixed chart is the given one up to the symmetry of the fibre products
  have h21 : IsClosedImmersion (pullback.map j₂ j₁ (j₂ ≫ w) (j₁ ≫ w) (𝟙 T₂) (𝟙 T₁) w
      (by simp) (by simp)) := by
    have := hd
    rw [pullback_map_symmetry w]
    infer_instance
  refine IsSeparated.of_openCover w (Scheme.Cover.mkOfCovers WalkingPair
    (fun k ↦ WalkingPair.casesOn k T₁ T₂) (fun k ↦ WalkingPair.casesOn k j₁ j₂)
    (fun x ↦ ?_) (fun k ↦ by cases k <;> infer_instance)) (fun i j ↦ ?_)
  · have hx : x ∈ Set.range j₁ ∪ Set.range j₂ := by
      rw [hcov]
      trivial
    obtain ⟨y, hy⟩ | ⟨y, hy⟩ := hx
    exacts [⟨WalkingPair.left, y, hy⟩, ⟨WalkingPair.right, y, hy⟩]
  · cases i <;> cases j
    exacts [isClosedImmersion_pullback_map_self w j₁, hd, h21,
      isClosedImmersion_pullback_map_self w j₂]

end TwoOpenCover

section SeparatingPair

set_option backward.defeqAttrib.useBackward true

/-- Two opens `U` and `V` of `X` form a *separating pair* if the ring of sections over `U ⊓ V`
is generated by the images of the restriction maps from `U` and from `V`. When `U`, `V` and
`U ⊓ V` are affine this says exactly that `U ⊓ V ⟶ U × V` is a closed immersion, see
`AlgebraicGeometry.isSeparatingPair_iff`. -/
def IsSeparatingPair (X : Scheme.{u}) (U V : X.Opens) : Prop :=
  Subring.closure
      (Set.range ⇑(X.homOfLE (inf_le_left : U ⊓ V ≤ U)).appTop.hom ∪
        Set.range ⇑(X.homOfLE (inf_le_right : U ⊓ V ≤ V)).appTop.hom) = ⊤

variable {X : Scheme.{u}}

/-- For affine `U`, `V` and `U ⊓ V`, being a separating pair means that the canonical immersion
`U ⊓ V ⟶ U × V` is a closed immersion. -/
lemma isSeparatingPair_iff (U V : X.Opens) [IsAffine U.toScheme] [IsAffine V.toScheme]
    [IsAffine (U ⊓ V : X.Opens).toScheme] :
    IsSeparatingPair X U V ↔
      IsClosedImmersion (pullback.mapDesc U.ι V.ι (terminal.from X)) := by
  have hsq := isPullback_opens_inf U V
  have hP : IsAffine (pullback U.ι V.ι) := .of_isIso hsq.isoPullback.inv
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion), and_iff_right hP]
  have hpush := isPushout_appTop_of_isPullback
    (IsPullback.of_hasPullback (U.ι ≫ terminal.from X) (V.ι ≫ terminal.from X))
  have htop := CommRingCat.closure_range_union_range_eq_top_of_isPushout hpush
  set φ := (pullback.mapDesc U.ι V.ι (terminal.from X)).appTop with hφ
  have m₁ : pullback.mapDesc U.ι V.ι (terminal.from X) ≫
      pullback.fst (U.ι ≫ terminal.from X) (V.ι ≫ terminal.from X) = pullback.fst U.ι V.ι := by
    simp
  have m₂ : pullback.mapDesc U.ι V.ι (terminal.from X) ≫
      pullback.snd (U.ι ≫ terminal.from X) (V.ι ≫ terminal.from X) = pullback.snd U.ι V.ι := by
    simp
  have key : Function.Surjective ⇑φ.hom ↔
      Subring.closure (Set.range ⇑(pullback.fst U.ι V.ι).appTop.hom ∪
        Set.range ⇑(pullback.snd U.ι V.ι).appTop.hom) = ⊤ := by
    have e₁ : (pullback.fst U.ι V.ι).appTop =
        (pullback.fst (U.ι ≫ terminal.from X) (V.ι ≫ terminal.from X)).appTop ≫ φ := by
      rw [hφ, ← Scheme.Hom.comp_appTop, m₁]
    have e₂ : (pullback.snd U.ι V.ι).appTop =
        (pullback.snd (U.ι ≫ terminal.from X) (V.ι ≫ terminal.from X)).appTop ≫ φ := by
      rw [hφ, ← Scheme.Hom.comp_appTop, m₂]
    rw [e₁, e₂]
    constructor
    · intro hs
      have := Subring.closure_image_eq_top φ.hom hs htop
      rwa [Set.image_union, ← Set.range_comp, ← Set.range_comp] at this
    · intro h x
      have hle : Subring.closure (Set.range ⇑((pullback.fst (U.ι ≫ terminal.from X)
            (V.ι ≫ terminal.from X)).appTop ≫ φ).hom ∪
          Set.range ⇑((pullback.snd (U.ι ≫ terminal.from X)
            (V.ι ≫ terminal.from X)).appTop ≫ φ).hom) ≤ φ.hom.range := by
        rw [Subring.closure_le]
        rintro y (⟨z, rfl⟩ | ⟨z, rfl⟩) <;> exact ⟨_, rfl⟩
      exact hle (h.ge (Subring.mem_top x))
  rw [key]
  have : IsIso hsq.isoPullback.hom.appTop := by
    refine ⟨hsq.isoPullback.inv.appTop, ?_, ?_⟩ <;>
      rw [← Scheme.Hom.comp_appTop] <;> simp
  refine Iff.trans ?_ (CommRingCat.closure_range_union_eq_top_iff_of_iso
    (a := (pullback.fst U.ι V.ι).appTop) (b := (pullback.snd U.ι V.ι).appTop)
    hsq.isoPullback.hom.appTop)
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
  rfl

/-- In a separated scheme any two affine opens form a separating pair. -/
lemma isSeparatingPair_of_isSeparated [Scheme.IsSeparated X] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsSeparatingPair X U V := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine (U ⊓ V : X.Opens).toScheme := hU.inf hV
  rw [isSeparatingPair_iff]
  have h1 : MorphismProperty.diagonal @IsClosedImmersion (terminal.from X) := by
    rw [← IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
    infer_instance
  exact HasAffineProperty.iff_of_isAffine.mpr
    ((HasAffineProperty.iff_of_isAffine
      (P := MorphismProperty.diagonal @IsClosedImmersion)).mp h1 U.ι V.ι)

/-- **The affine criterion for separatedness**: a scheme covered by affine opens which pairwise
have affine intersections and form separating pairs is separated. -/
lemma Scheme.isSeparated_of_isSeparatingPair {ι : Type*} (U : ι → X.Opens)
    (hcov : TopologicalSpace.IsOpenCover U) (hU : ∀ a, IsAffineOpen (U a))
    (hinf : ∀ a b, IsAffineOpen (U a ⊓ U b))
    (h : ∀ a b, IsSeparatingPair X (U a) (U b)) : Scheme.IsSeparated X := by
  have (a : ι) : IsAffine (U a).toScheme := hU a
  have (i : ι) : IsAffine ((X.openCoverOfIsOpenCover U hcov).X i) := hU i
  let := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  constructor
  rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
  refine HasAffineProperty.iff_of_isAffine.mpr
    (AffineTargetMorphismProperty.diagonal_of_openCover_source _
      (X.openCoverOfIsOpenCover U hcov) fun a b ↦ ?_)
  have : IsAffine (U a ⊓ U b : X.Opens).toScheme := hinf a b
  exact HasAffineProperty.iff_of_isAffine.mp ((isSeparatingPair_iff (U a) (U b)).mp (h a b))

end SeparatingPair

/-- A scheme admitting a separated morphism to a separated scheme is separated. -/
lemma Scheme.isSeparated_of_isSeparated_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
    [Y.IsSeparated] : X.IsSeparated :=
  ⟨by rw [← terminal.comp_from f]; infer_instance⟩

section SchemeTheoreticallyDominant

/-- **Morphisms into a separated target agreeing on a scheme-theoretically dominant
subscheme are equal.** Suppose `f g : T ⟶ Y` agree over some separated `s : Y ⟶ Z`.
Then `f = g` as soon as `ι ≫ f = ι ≫ g` for some scheme-theoretically dominant
`ι : W ⟶ T`.

This is `AlgebraicGeometry.ext_of_isDominant_of_isSeparated` with dominance of `ι`
strengthened to scheme-theoretic dominance and, in exchange, the reducedness assumption
on `T` dropped. -/
theorem ext_of_isSchemeTheoreticallyDominant_of_isSeparated {W T Y Z : Scheme.{u}}
    {f g : T ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ T) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let T' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let W' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : T' ⟶ Y' := Over.homMk f
  let g' : T' ⟶ Y' := Over.homMk g
  let ι' : W' ⟶ T' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  -- `ι` factors through the equalizer of `f` and `g`, which is a closed immersion
  have hfac : (equalizer.lift ι' (by ext1; exact hU)).left ≫ (equalizer.ι f' g').left = ι := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  -- hence the equalizer has trivial kernel, so it is an isomorphism
  have : IsIso (equalizer.ι f' g').left := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ← le_bot_iff, ← ι.ker_eq_bot, ← hfac]
    exact Scheme.Hom.le_ker_comp _ _
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

/-- **Morphisms of `S`-schemes into a separated `S`-scheme agreeing on a
scheme-theoretically dominant subscheme are equal.** For `S`-morphisms `f g : T ⟶ Y`
into a separated `S`-scheme `Y`, `f = g` as soon as `ι ≫ f = ι ≫ g` for some
scheme-theoretically dominant `ι : W ⟶ T`.

This is `AlgebraicGeometry.ext_of_isDominant_of_isSeparated'` with dominance of `ι`
strengthened to scheme-theoretic dominance and, in exchange, the reducedness assumption
on `T` dropped. -/
theorem ext_of_isSchemeTheoreticallyDominant_of_isSeparated' (S : Scheme.{u})
    {T Y : Scheme.{u}} [T.Over S] [Y.Over S] [IsSeparated (Y ↘ S)] {f g : T ⟶ Y}
    [f.IsOver S] [g.IsOver S] {W : Scheme.{u}} (ι : W ⟶ T)
    [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isSchemeTheoreticallyDominant_of_isSeparated (Y ↘ S) (by simp) ι hU


end SchemeTheoreticallyDominant

end AlgebraicGeometry
