/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange

/-!
# Purity for regular closed immersions: intersections and exterior products

Let `i₁ : Y₁ ⟶ X` and `i₂ : Y₂ ⟶ X` be regular closed immersions of codimensions `c₁`, `c₂` into a
scheme `X` smooth over a perfect field, meeting transversally: their intersection
`Y = Y₁ ×_X Y₂ ⟶ X` is a regular closed immersion of codimension `c₁ + c₂`. Then the fundamental
class of `Y` is the cup product with supports of those of `Y₁` and `Y₂`,
`[Y ⊂ X] = [Y₁ ⊂ X] ∪ [Y₂ ⊂ X]`: near a point of `Y`, frames `f` of `Y₁` and `g` of `Y₂` give the
frame `(f, g)` of `Y` (`AlgebraicGeometry.Scheme.Hom.EtaleFrame.inter`), whose class
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(g_{c₂})` is the cup product of the classes of the two frames
(`AlgebraicGeometry.Etale.kummerBoundaryProduct_append`).

Applied to `Z₁ ×_k X₂` and `X₁ ×_k Z₂` in `X₁ ×_k X₂`, whose fundamental classes are the
pullbacks of `[Z₁ ⊂ X₁]` and `[Z₂ ⊂ X₂]` along the smooth projections
(`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_smooth`), this gives the
compatibility with exterior products of clause (d) of blueprint `lemma-class-of-point--1`,
`[Z₁ × Z₂ ⊂ X₁ × X₂] = [Z₁ ⊂ X₁] ⊠ [Z₂ ⊂ X₂]`.

## Main statements

- `AlgebraicGeometry.Etale.restrictSupportedClass_cupWithSupportsTateObject`: restriction of
  supports commutes with the cup product of Tate classes.
- `AlgebraicGeometry.Etale.fundamentalClass_eq_cupWithSupportsTateObject_of_isPullback`: the
  intersection formula.
- `AlgebraicGeometry.Etale.fundamentalClass_eq_cupWithSupportsTateObject`: exterior products.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- The range of the pullback of two morphisms of schemes is the intersection of their ranges. -/
lemma Scheme.range_eq_inter_of_isPullback {X Y₁ Y₂ Y : Scheme.{u}}
    {i₁ : Y₁ ⟶ X} {i₂ : Y₂ ⟶ X} {i : Y ⟶ X} {j₁ : Y ⟶ Y₁} {j₂ : Y ⟶ Y₂}
    (hY : IsPullback j₁ j₂ i₁ i₂) (hi : j₁ ≫ i₁ = i) :
    Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨⟨j₁ y, ?_⟩, ⟨j₂ y, ?_⟩⟩
    · rw [← hi, Scheme.Hom.comp_apply]
    · rw [← hi, hY.w, Scheme.Hom.comp_apply]
  · rintro ⟨⟨y₁, rfl⟩, ⟨y₂, hy⟩⟩
    obtain ⟨y, hy₁, -⟩ := hY.exists_scheme_point y₁ y₂ hy.symm
    exact ⟨y, by rw [← hi, Scheme.Hom.comp_apply, hy₁]⟩

/-- `Z₁ ×_k Z₂` is the intersection of `Z₁ ×_k X₂` and `X₁ ×_k Z₂` in `X₁ ×_k X₂`. -/
lemma isPullback_pullbackMap_pullbackSnd {k : Type u} [Field k] {X₁ X₂ Z₁ Z₂ : Scheme.{u}}
    (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) (a₁ : X₁ ⟶ Spec (.of k)) (a₂ : X₂ ⟶ Spec (.of k)) :
    IsPullback
      (pullback.lift (pullback.fst (i₁ ≫ a₁) (i₂ ≫ a₂))
        (pullback.map (i₁ ≫ a₁) (i₂ ≫ a₂) a₁ a₂ i₁ i₂ (𝟙 _) (by simp) (by simp))
        (by simp) : pullback (i₁ ≫ a₁) (i₂ ≫ a₂) ⟶ pullback i₁ (pullback.fst a₁ a₂))
      (pullback.lift (pullback.snd (i₁ ≫ a₁) (i₂ ≫ a₂))
        (pullback.map (i₁ ≫ a₁) (i₂ ≫ a₂) a₁ a₂ i₁ i₂ (𝟙 _) (by simp) (by simp))
        (by simp) : pullback (i₁ ≫ a₁) (i₂ ≫ a₂) ⟶ pullback i₂ (pullback.snd a₁ a₂))
      (pullback.snd i₁ (pullback.fst a₁ a₂)) (pullback.snd i₂ (pullback.snd a₁ a₂)) := by
  refine IsPullback.of_isLimit' ⟨by simp⟩ (PullbackCone.IsLimit.mk _
    (fun s ↦ pullback.lift (s.fst ≫ pullback.fst _ _) (s.snd ≫ pullback.fst _ _) ?_) ?_ ?_ ?_)
  · have h₁ := pullback.condition (f := i₁) (g := pullback.fst a₁ a₂)
    have h₂ := pullback.condition (f := i₂) (g := pullback.snd a₁ a₂)
    have h := pullback.condition (f := a₁) (g := a₂)
    simp only [Category.assoc]
    rw [reassoc_of% h₁, reassoc_of% h₂, h, ← Category.assoc s.fst, s.condition,
      Category.assoc]
  · intro s
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext
      · simp
      · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc,
          cospan_right, pullback.fst_comp_eq_toBase]
        rw [← pullback.snd_comp_eq_toBase]
        simpa using (s.condition =≫ pullback.snd a₁ a₂).symm
  · intro s
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext
      · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc,
          cospan_left, pullback.fst_comp_eq_toBase]
        rw [← pullback.snd_comp_eq_toBase]
        simpa using s.condition =≫ pullback.fst a₁ a₂
      · simp
  · intro s m h₁ h₂
    apply pullback.hom_ext
    · simpa using congrArg (· ≫ pullback.fst i₁ (pullback.fst a₁ a₂)) h₁
    · simpa using congrArg (· ≫ pullback.fst i₂ (pullback.snd a₁ a₂)) h₂

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

/-- Restriction of supports along any `e : U' ⟶ U` commutes with the cup product with supports
of Tate classes (`AlgebraicGeometry.Etale.cupWithSupportsTateObject`). -/
theorem restrictSupportedClass_cupWithSupportsTateObject {U U' Z₁ Z₂ Z Z₁' Z₂' Z' : Scheme.{u}}
    [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ U'] (e : U' ⟶ U)
    (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U) (i₁' : Z₁' ⟶ U') (i₂' : Z₂' ⟶ U') (i' : Z' ⟶ U')
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂'] [IsClosedImmersion i']
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base)
    (h' : Set.range i'.base = Set.range i₁'.base ∩ Set.range i₂'.base)
    (g₁ : Z₁' ⟶ Z₁) (g₂ : Z₂' ⟶ Z₂) (g : Z' ⟶ Z) (hg₁ : IsPullback g₁ i₁' i₁ e)
    (hg₂ : IsPullback g₂ i₂' i₂ e) (hg : IsPullback g i' i e) {m m' : ℤ}
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv
        (leftDerivedUpperStarTateShiftIso Λ e (m + m'))
        (cupWithSupportsTateObject Λ i₁ i₂ i h α β) =
      cupWithSupportsTateObject Λ i₁' i₂' i' h'
        (restrictSupportedClass Λ e i₁ i₁' g₁ hg₁
          (leftDerivedUpperStarConstantComplexIso Λ e).inv
          (leftDerivedUpperStarTateShiftIso Λ e m) α)
        (restrictSupportedClass Λ e i₂ i₂' g₂ hg₂
          (leftDerivedUpperStarConstantComplexIso Λ e).inv
          (leftDerivedUpperStarTateShiftIso Λ e m') β) := by
  simp only [cupWithSupportsTateObject]
  rw [restrictSupportedClass_map _ e _ _ g hg _
    (leftDerivedUpperStarTensorIso _ e _ _ ≪≫
      ((derivedTensor _ U').mapIso (leftDerivedUpperStarTateShiftIso Λ e m)).app _ ≪≫
        ((derivedTensor _ U').obj _).mapIso (leftDerivedUpperStarTateShiftIso Λ e m'))
    _ _ _ (by
      rw [leftDerivedUpperStar_map_shiftTateObjectAddIso]
      simp only [derivedTensorHom, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
        Category.assoc]; rfl),
    restrictSupportedClass_cupWithSupports _ e _ _ _ _ _ _ _ _ _ _ g hg₁ hg₂ hg _ _ _ _ _
      (constantComplexDiagonal_comp_derivedTensorHom Λ e)]

variable [HasKummerClass.IsNormalized Λ] {X : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]

/-- The fundamental class does not depend on how the structure morphism is written. -/
lemma fundamentalClass_congr [HasInvertibleExponent Λ X] {Z : Scheme.{u}} (c : ℕ) (i : Z ⟶ X)
    [IsRegularImmersion c i] {aX aX' : X ⟶ Spec (.of k)} [Smooth aX] [Smooth aX']
    (h : aX = aX') (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    fundamentalClass Λ c i aX hZ = fundamentalClass Λ c i aX' hZ := by
  subst h
  rfl

/-- Blueprint `prop-pur-regular-immersion-purity-compatibilities`: Compatibilities of purity for
regular immersions

**Transverse intersections: the intersection formula.** Let `i₁ : Y₁ ⟶ X` and `i₂ : Y₂ ⟶ X` be
regular closed immersions of codimensions `c₁` and `c₂` meeting transversally: their
intersection `Y = Y₁ ×_X Y₂ ⟶ X` is regular of codimension `c₁ + c₂`. Then
`[Y ⊂ X] = [Y₁ ⊂ X] ∪ [Y₂ ⊂ X]`, with the twist additivity `Λ(c₁) ⊗ Λ(c₂) ≅ Λ(c₁ + c₂)`. This is
the content of item 2 of the blueprint node (transverse composition): near every point of `Y`,
frames `f` of `Y₁` and `g` of `Y₂` give the frame `(f, g)` of `Y`, whose class
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(g_{c₂})` is the cup product of the classes of the two frames
(`AlgebraicGeometry.Etale.kummerBoundaryProduct_append`). -/
theorem fundamentalClass_eq_cupWithSupportsTateObject_of_isPullback [HasInvertibleExponent Λ X]
    {Y₁ Y₂ Y : Scheme.{u}} (c₁ c₂ : ℕ) (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) (i : Y ⟶ X)
    [IsRegularImmersion c₁ i₁] [IsRegularImmersion c₂ i₂] [IsRegularImmersion (c₁ + c₂) i]
    {j₁ : Y ⟶ Y₁} {j₂ : Y ⟶ Y₂} (hY : IsPullback j₁ j₂ i₁ i₂) (hi : j₁ ≫ i₁ = i)
    (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hY₁ : ∀ y : Y₁, IsRegularLocalRing (Y₁.presheaf.stalk y))
    (hY₂ : ∀ y : Y₂, IsRegularLocalRing (Y₂.presheaf.stalk y))
    (hYr : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) :
    fundamentalClass Λ (c₁ + c₂) i aX hYr =
      cupWithSupportsTateObject Λ i₁ i₂ i (Scheme.range_eq_inter_of_isPullback hY hi)
        (fundamentalClass Λ c₁ i₁ aX hY₁) (fundamentalClass Λ c₂ i₂ aX hY₂) ≫
        eqToHom (by rw [Nat.cast_add]) := by
  refine eq_of_forall_exists_frameRestriction_eq Λ (c₁ + c₂) i aX hYr fun y ↦ ?_
  obtain ⟨F₁, hF₁, hy₁, -, -⟩ := i₁.exists_etaleFrame_isOpenImmersion c₁ (j₁ y)
  obtain ⟨F₂, hF₂, hy₂, -, -⟩ := i₂.exists_etaleFrame_isOpenImmersion c₂ (j₂ y)
  let F := Scheme.Hom.EtaleFrame.inter hY hi F₁ F₂
  let a₁ := pullback.fst F₁.e F₂.e
  let a₂ := pullback.snd F₁.e F₂.e
  have ha₁ : F.e = a₁ ≫ F₁.e := rfl
  have ha₂ : F.e = a₂ ≫ F₂.e := pullback.condition
  refine ⟨F, inferInstanceAs (IsOpenImmersion (a₁ ≫ F₁.e)),
    Scheme.Hom.EtaleFrame.mem_range_inter_toZ hY hi F₁ F₂ y hy₁ hy₂, ?_⟩
  have : HasInvertibleExponent Λ F.U := .of_hom F.e
  have : HasInvertibleExponent Λ (pullback F₁.e F₂.e) := .of_hom (pullback.fst F₁.e F₂.e ≫ F₁.e)
  have : HasInvertibleExponent Λ F₁.U := .of_hom F₁.e
  have : HasInvertibleExponent Λ F₂.U := .of_hom F₂.e
  let f₁ : Fin c₁ → Γ(F.U, ⊤) := fun t ↦ a₁.appTop (F₁.f t)
  let f₂ : Fin c₂ → Γ(F.U, ⊤) := fun t ↦ a₂.appTop (F₂.f t)
  obtain ⟨g₁, hg₁⟩ : ∃ g, IsPullback g (F.U.zeroLocusSubschemeι (Set.range f₁))
      (F₁.U.zeroLocusSubschemeι (Set.range F₁.f)) a₁ :=
    ⟨_, isPullback_zeroLocusSubschemeι a₁ _ _ (by rw [← Set.range_comp]; rfl)⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g, IsPullback g (F.U.zeroLocusSubschemeι (Set.range f₂))
      (F₂.U.zeroLocusSubschemeι (Set.range F₂.f)) a₂ :=
    ⟨_, isPullback_zeroLocusSubschemeι a₂ _ _ (by rw [← Set.range_comp]; rfl)⟩
  have hp₁ : IsPullback (g₁ ≫ F₁.toZ) (F.U.zeroLocusSubschemeι (Set.range f₁)) i₁ F.e :=
    hg₁.paste_horiz F₁.isPullback
  have hp₂ : IsPullback (g₂ ≫ F₂.toZ) (F.U.zeroLocusSubschemeι (Set.range f₂)) i₂ F.e :=
    ha₂ ▸ hg₂.paste_horiz F₂.isPullback
  -- the restrictions of the fundamental classes of `Y₁` and `Y₂` are the frame classes
  have e₁ : restrictSupportedClass Λ F.e i₁ _ _ hp₁
      (leftDerivedUpperStarConstantComplexIso Λ F.e).inv
      (leftDerivedUpperStarTateShiftIso Λ F.e c₁) (fundamentalClass Λ c₁ i₁ aX hY₁) =
        kummerBoundaryProduct Λ f₁ := by
    rw [restrictSupportedClass_comp_tateShift Λ a₁ F₁.e F.e ha₁ _ _ _ F₁.toZ F₁.isPullback g₁
      hg₁ _ hp₁]
    have h := frameRestriction_fundamentalClass Λ c₁ i₁ aX hY₁ F₁
    rw [frameRestriction] at h
    rw [h]
    exact restrictSupportedClass_kummerBoundaryProduct Λ a₁ F₁.f f₁ (fun _ ↦ rfl) g₁ hg₁
  have e₂ : restrictSupportedClass Λ F.e i₂ _ _ hp₂
      (leftDerivedUpperStarConstantComplexIso Λ F.e).inv
      (leftDerivedUpperStarTateShiftIso Λ F.e c₂) (fundamentalClass Λ c₂ i₂ aX hY₂) =
        kummerBoundaryProduct Λ f₂ := by
    rw [restrictSupportedClass_comp_tateShift Λ a₂ F₂.e F.e ha₂ _ _ _ F₂.toZ F₂.isPullback g₂
      hg₂ _ hp₂]
    have h := frameRestriction_fundamentalClass Λ c₂ i₂ aX hY₂ F₂
    rw [frameRestriction] at h
    rw [h]
    exact restrictSupportedClass_kummerBoundaryProduct Λ a₂ F₂.f f₂ (fun _ ↦ rfl) g₂ hg₂
  rw [frameRestriction_fundamentalClass, frameRestriction,
    restrictSupportedClass_comp_eqToHom Λ F.e _ _ _ _ (by push_cast; rfl),
    restrictSupportedClass_cupWithSupportsTateObject Λ F.e i₁ i₂ i _ _
      (F.U.zeroLocusSubschemeι (Set.range F.f)) _
      (by rw [Scheme.Hom.EtaleFrame.inter_f, Fin.range_append,
        Scheme.range_zeroLocusSubschemeι_union]) _ _ _ hp₁ hp₂, e₁, e₂]
  exact kummerBoundaryProduct_append Λ f₁ f₂

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

Blueprint `prop-pur-regular-immersion-purity-compatibilities` (item 3, cup products).

**(d) Exterior products**,
`[Z₁ × Z₂ ⊂ X₁ × X₂] = [Z₁ ⊂ X₁] ⊠ [Z₂ ⊂ X₂]`. Let `(X₁, Z₁)` and `(X₂, Z₂)` be pairs as in the
theorem over the same perfect field `k`, of codimensions `c₁` and `c₂`, let
`P = X₁ ×_k X₂` with projections `p₁`, `p₂`, let `Z₁ ×_k X₂ ⟶ P` and `X₁ ×_k Z₂ ⟶ P` be the base
changes of `i₁` and `i₂` along them, and `i₁₂ : Z₁ ×_k Z₂ ⟶ P` the product of `i₁` and `i₂`, the
closed immersion of their intersection. Then the fundamental class of `i₁₂` is the cup product
with supports of the restrictions `p₁^* [Z₁ ⊂ X₁]` and `p₂^* [Z₂ ⊂ X₂]`. These restrictions are
the fundamental classes of `Z₁ ×_k X₂` and `X₁ ×_k Z₂`
(`AlgebraicGeometry.Etale.restrictSupportedClass_fundamentalClass_of_smooth`), and the
intersection formula
(`AlgebraicGeometry.Etale.fundamentalClass_eq_cupWithSupportsTateObject_of_isPullback`) applies.

The hypotheses on the product are derived: `i₁₂` is a regular immersion of codimension
`c₁ + c₂` (`AlgebraicGeometry.IsRegularImmersion.pullback_map`), `Z₁ ×_k Z₂` is regular
(`AlgebraicGeometry.isRegularLocalRing_stalk_pullback`), `P` is smooth over `k` and the exponent
of `Λ` is invertible on `P`. -/
theorem fundamentalClass_eq_cupWithSupportsTateObject {X₁ X₂ Z₁ Z₂ : Scheme.{u}} (c₁ c₂ : ℕ)
    (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) [IsRegularImmersion c₁ i₁] [IsRegularImmersion c₂ i₂]
    (a₁ : X₁ ⟶ Spec (.of k)) (a₂ : X₂ ⟶ Spec (.of k)) [Smooth a₁] [Smooth a₂]
    [HasInvertibleExponent Λ X₁] [HasInvertibleExponent Λ X₂]
    (hZ₁ : ∀ z : Z₁, IsRegularLocalRing (Z₁.presheaf.stalk z))
    (hZ₂ : ∀ z : Z₂, IsRegularLocalRing (Z₂.presheaf.stalk z)) :
    haveI := IsRegularImmersion.pullback_map c₁ c₂ i₁ i₂ a₁ a₂
    haveI : HasInvertibleExponent Λ (pullback a₁ a₂) := .of_hom (pullback.fst a₁ a₂)
    fundamentalClass Λ (c₁ + c₂) (pullback.map (i₁ ≫ a₁) (i₂ ≫ a₂) a₁ a₂ i₁ i₂ (𝟙 _)
        (by simp) (by simp)) (pullback.fst a₁ a₂ ≫ a₁)
        (isRegularLocalRing_stalk_pullback (i₁ ≫ a₁) (i₂ ≫ a₂) hZ₁ hZ₂) =
      cupWithSupportsTateObject Λ (pullback.snd i₁ (pullback.fst a₁ a₂))
        (pullback.snd i₂ (pullback.snd a₁ a₂))
        (pullback.map (i₁ ≫ a₁) (i₂ ≫ a₂) a₁ a₂ i₁ i₂ (𝟙 _) (by simp) (by simp))
        (Scheme.Pullback.range_map_eq_inter _ _ _ _ _ _ _)
        (restrictSupportedClass Λ (pullback.fst a₁ a₂) i₁ _ _
          (IsPullback.of_hasPullback _ _)
          (leftDerivedUpperStarConstantComplexIso Λ _).inv
          (leftDerivedUpperStarTateShiftIso Λ _ c₁) (fundamentalClass Λ c₁ i₁ a₁ hZ₁))
        (restrictSupportedClass Λ (pullback.snd a₁ a₂) i₂ _ _
          (IsPullback.of_hasPullback _ _)
          (leftDerivedUpperStarConstantComplexIso Λ _).inv
          (leftDerivedUpperStarTateShiftIso Λ _ c₂) (fundamentalClass Λ c₂ i₂ a₂ hZ₂)) ≫
        eqToHom (by rw [Nat.cast_add]) := by
  have := IsRegularImmersion.pullback_map c₁ c₂ i₁ i₂ a₁ a₂
  have : HasInvertibleExponent Λ (pullback a₁ a₂) := .of_hom (pullback.fst a₁ a₂)
  have h₁ := IsPullback.of_hasPullback i₁ (pullback.fst a₁ a₂)
  have h₂ := IsPullback.of_hasPullback i₂ (pullback.snd a₁ a₂)
  have := IsRegularImmersion.of_isPullback c₁ h₁
  have := IsRegularImmersion.of_isPullback c₂ h₂
  rw [restrictSupportedClass_fundamentalClass_of_smooth Λ c₁ i₁ a₁ hZ₁ _ _ _ h₁,
    restrictSupportedClass_fundamentalClass_of_smooth Λ c₂ i₂ a₂ hZ₂ _ _ _ h₂,
    fundamentalClass_congr Λ c₂ _ (pullback.condition (f := a₁) (g := a₂)).symm]
  exact fundamentalClass_eq_cupWithSupportsTateObject_of_isPullback Λ c₁ c₂ _ _ _
    (isPullback_pullbackMap_pullbackSnd i₁ i₂ a₁ a₂) (pullback.lift_snd _ _ _) _ _ _ _

end Etale

end AlgebraicGeometry
