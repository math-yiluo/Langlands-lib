/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Base change of binary coproducts of schemes

Given `v₁ : V₁ ⟶ W`, `v₂ : V₂ ⟶ W` and `π : W' ⟶ W`, the base changes of the coproduct
inclusions exhibit `(V₁ ⨿ V₂) ×_W W'` as the coproduct of `V₁ ×_W W'` and `V₂ ×_W W'`.
This is the universality of coproducts of schemes, in the form needed to split the base change
of a disjoint union.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {V₁ V₂ W W' : Scheme.{u}} (v₁ : V₁ ⟶ W) (v₂ : V₂ ⟶ W) (π : W' ⟶ W)

/-- The base change of the first coproduct inclusion. -/
noncomputable abbrev pullbackCoprodInl : pullback v₁ π ⟶ pullback (coprod.desc v₁ v₂) π :=
  pullback.map v₁ π (coprod.desc v₁ v₂) π coprod.inl (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The base change of the second coproduct inclusion. -/
noncomputable abbrev pullbackCoprodInr : pullback v₂ π ⟶ pullback (coprod.desc v₁ v₂) π :=
  pullback.map v₂ π (coprod.desc v₁ v₂) π coprod.inr (𝟙 _) (𝟙 _) (by simp) (by simp)

lemma isPullback_pullbackCoprodInl :
    IsPullback (pullback.fst v₁ π) (pullbackCoprodInl v₁ v₂ π) (coprod.inl : V₁ ⟶ V₁ ⨿ V₂)
      (pullback.fst (coprod.desc v₁ v₂) π) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback _ _)
  simpa using IsPullback.of_hasPullback v₁ π

lemma isPullback_pullbackCoprodInr :
    IsPullback (pullback.fst v₂ π) (pullbackCoprodInr v₁ v₂ π) (coprod.inr : V₂ ⟶ V₁ ⨿ V₂)
      (pullback.fst (coprod.desc v₁ v₂) π) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback _ _)
  simpa using IsPullback.of_hasPullback v₂ π

lemma range_pullbackCoprodInl :
    Set.range (pullbackCoprodInl v₁ v₂ π).base =
      (pullback.fst (coprod.desc v₁ v₂) π).base ⁻¹' Set.range (coprod.inl : V₁ ⟶ V₁ ⨿ V₂).base := by
  have := Scheme.image_preimage_eq_of_isPullback (isPullback_pullbackCoprodInl v₁ v₂ π) Set.univ
  simpa [Set.image_univ] using this

lemma range_pullbackCoprodInr :
    Set.range (pullbackCoprodInr v₁ v₂ π).base =
      (pullback.fst (coprod.desc v₁ v₂) π).base ⁻¹' Set.range (coprod.inr : V₂ ⟶ V₁ ⨿ V₂).base := by
  have := Scheme.image_preimage_eq_of_isPullback (isPullback_pullbackCoprodInr v₁ v₂ π) Set.univ
  simpa [Set.image_univ] using this

/-- The base changes of the coproduct inclusions have complementary images. -/
lemma isCompl_opensRange_pullbackCoprodInl_pullbackCoprodInr :
    IsCompl (pullbackCoprodInl v₁ v₂ π).opensRange (pullbackCoprodInr v₁ v₂ π).opensRange := by
  have h := (isCompl_range_inl_inr V₁ V₂).map
    (CompleteLatticeHom.setPreimage (pullback.fst (coprod.desc v₁ v₂) π).base)
  rw [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj,
    ← TopologicalSpace.Opens.coe_inj]
  simp only [Scheme.Hom.coe_opensRange, range_pullbackCoprodInl, range_pullbackCoprodInr,
    TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_bot,
    TopologicalSpace.Opens.coe_top]
  exact ⟨h.inf_eq_bot, h.sup_eq_top⟩

/-- Coproducts of schemes are universal: `(V₁ ⨿ V₂) ×_W W'` is the coproduct of `V₁ ×_W W'`
and `V₂ ×_W W'`. -/
lemma nonempty_isColimit_binaryCofan_pullbackCoprod :
    Nonempty (IsColimit (BinaryCofan.mk (pullbackCoprodInl v₁ v₂ π)
      (pullbackCoprodInr v₁ v₂ π))) :=
  nonempty_isColimit_binaryCofanMk_of_isCompl _ _
    (isCompl_opensRange_pullbackCoprodInl_pullbackCoprodInr v₁ v₂ π)

end AlgebraicGeometry

namespace AlgebraicGeometry

section

variable {X Y : Scheme.{u}}

/-- A property local at the source holds for `coprod.desc f g` if it holds for `f` and `g`. -/
lemma IsZariskiLocalAtSource.coprodDesc (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] {Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z} (hf : P f) (hg : P g) :
    P (coprod.desc f g) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (coprodOpenCover.{_, 0} X Y)]
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · simpa [coprodOpenCover] using hf
  · simpa [coprodOpenCover] using hg

instance [CompactSpace X] [CompactSpace Y] : CompactSpace (X ⨿ Y : Scheme.{u}) :=
  (coprodMk X Y).compactSpace

/-- The disjoint union of two quasi-affine schemes is quasi-affine. -/
instance IsQuasiAffine.coprod [Scheme.IsQuasiAffine X] [Scheme.IsQuasiAffine Y] :
    Scheme.IsQuasiAffine (X ⨿ Y : Scheme.{u}) := by
  have : IsOpenImmersion (coprod.map X.toSpecΓ Y.toSpecΓ) :=
    IsZariskiLocalAtTarget.coprodMap (P := @IsOpenImmersion) _ _ inferInstance inferInstance
  exact Scheme.IsQuasiAffine.of_isImmersion (coprod.map X.toSpecΓ Y.toSpecΓ)

end

end AlgebraicGeometry
