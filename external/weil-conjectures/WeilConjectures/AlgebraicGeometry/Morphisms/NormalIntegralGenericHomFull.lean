/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Fullness of finite étale restriction to the generic point

## References

* Stacks Project, Tag 0BQM, full faithfulness in the proof
* Stacks Project, Tag 0BQM, full faithfulness of generic-point restriction
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Any morphism between the generic restrictions of finite étale covers of a
normal integral scheme extends uniquely over that scheme. -/
theorem finiteEtale_normalIntegral_generic_hom_full {B : Scheme.{u}} [IsIntegral B]
    (hB : ∀ x : B, IsIntegrallyClosed (B.presheaf.stalk x))
    {X Y Xη Yη : Scheme.{u}} (πX : X ⟶ B) (πY : Y ⟶ B)
    [IsFinite πX] [Etale πX] [IsFinite πY] [Etale πY]
    (πXη : Xη ⟶ Spec B.functionField) (πYη : Yη ⟶ Spec B.functionField)
    (ψX : Xη ⟶ X) (ψY : Yη ⟶ Y)
    (hX : IsPullback ψX πXη πX (B.fromSpecStalk (genericPoint B)))
    (hY : IsPullback ψY πYη πY (B.fromSpecStalk (genericPoint B)))
    (fη : Xη ⟶ Yη) (hfη : fη ≫ πYη = πXη) :
    ∃! f : X ⟶ Y, f ≫ πY = πX ∧ ψX ≫ f = fη ≫ ψY := by
  -- Normalization of the generic point is B, and remains trivial after smooth base change.
  let j := B.fromSpecFunctionField
  have hn : IsIso j.fromNormalization := by
    have := B.isIso_fromNormalization_restrict ⊤ (fun x _ ↦ hB x)
    have : IsIso (⊤ : B.Opens).ι := B.topIso.isIso_hom
    have : IsIso (B.fromNormalization ⁻¹ᵁ ⊤).ι := by
      simpa using B.normalization.topIso.isIso_hom
    have : IsIso ((B.fromNormalization ∣_ ⊤) ≫ (⊤ : B.Opens).ι) := inferInstance
    rw [morphismRestrict_ι] at this
    exact (isIso_comp_left_iff _ _).mp this
  let k := pullback.snd j πX
  have hk : IsIso k.fromNormalization := by
    rw [← Hom.normalizationPullback_snd j πX]
    infer_instance
  let e := hX.flip.isoPullback
  let a := e.inv ≫ fη ≫ ψY
  have ha : a ≫ πY = k ≫ πX := by
    dsimp only [a]
    rw [Category.assoc, Category.assoc, hY.w, ← Category.assoc fη, hfη]
    rw [← Category.assoc, hX.flip.isoPullback_inv_fst]
    exact pullback.condition
  -- View the generic morphism as a generic section of the finite morphism Y ×_B X → X.
  let b := pullback.lift a k ha
  let q := pullback.snd πY πX
  have hb : k = b ≫ q := by simp [b, q]
  let d := k.normalizationDesc b q hb
  let s := inv k.fromNormalization ≫ d
  have hs : s ≫ q = 𝟙 X := by
    dsimp only [s, d]
    rw [Category.assoc, Hom.normalizationDesc_comp, IsIso.inv_hom_id]
  have hc : ψX ≫ s = e.hom ≫ b := by
    have hkn : k.toNormalization = k ≫ inv k.fromNormalization := by
      apply (cancel_mono k.fromNormalization).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Hom.toNormalization_fromNormalization]
    have hed : e.hom ≫ k = ψX := hX.flip.isoPullback_hom_snd
    rw [← hed, Category.assoc]
    dsimp only [s]
    rw [← Category.assoc k, ← hkn, Hom.toNormalization_normalizationDesc]
  let f := s ≫ pullback.fst πY πX
  have hf : f ≫ πY = πX := by
    dsimp only [f]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  have hfc : ψX ≫ f = fη ≫ ψY := by
    dsimp only [f]
    rw [← Category.assoc, hc, Category.assoc]
    simp [b, a]
  refine ⟨f, ⟨hf, hfc⟩, ?_⟩
  rintro g ⟨hg, hgc⟩
  let t := pullback.lift g (𝟙 X) (by simpa using hg)
  have ht : t ≫ q = 𝟙 X := by simp [t, q]
  -- Uniqueness is the uniqueness in normalization's universal property.
  have hts : t = s := by
    apply (cancel_epi k.fromNormalization).mp
    apply Hom.normalization.hom_ext k _ _ q
    · simp only [← Category.assoc, Hom.toNormalization_fromNormalization]
      apply (cancel_epi e.hom).mp
      rw [← Category.assoc, hX.flip.isoPullback_hom_snd, ← Category.assoc,
        hX.flip.isoPullback_hom_snd, hc]
      apply pullback.hom_ext
      · simpa [t, b, a] using hgc
      · simp only [t, b, Category.assoc, pullback.lift_snd, Category.comp_id]
        exact hX.flip.isoPullback_hom_snd.symm
    · simp only [Category.assoc, ht, Category.comp_id]
    · simp only [Category.assoc, hs, Category.comp_id]
  simpa [t, f] using congrArg (fun z ↦ z ≫ pullback.fst πY πX) hts

end AlgebraicGeometry.Scheme
