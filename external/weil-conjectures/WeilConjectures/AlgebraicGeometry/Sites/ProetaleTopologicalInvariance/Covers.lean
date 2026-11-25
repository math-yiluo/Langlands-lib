/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Pro-étale coverings and base change along universal homeomorphisms

Let `r : X ⟶ Y` be a universal homeomorphism and let
`MorphismProperty.Over.pullback @WeaklyEtale ⊤ r : Y.ProEt ⥤ X.ProEt` be base change along `r`.
We show that this functor preserves and reflects coverings of the pro-étale topologies, and that
it is locally faithful.

## Main results

- `AlgebraicGeometry.Scheme.ofArrows_mem_proetalePrecoverage_of_comp`: a family of weakly étale
  morphisms to `V` is a pro-étale covering family if, after pulling back along a quasi-compact
  surjective `p : V' ⟶ V`, it is refined by a pro-étale covering family of `V'`.
- `AlgebraicGeometry.Scheme.ProEt.functorPushforward_overPullback_mem_topology_iff`: base change
  along a universal homeomorphism preserves and reflects pro-étale covering sieves.
- `AlgebraicGeometry.Scheme.ProEt.isLocallyFaithful_overPullback`: base change along a universal
  homeomorphism is locally faithful for the pro-étale topologies.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Let `p : V' ⟶ V` be quasi-compact and surjective, and let `f i : Z i ⟶ V` be weakly étale.
If there is a pro-étale covering family `f' j : Z' j ⟶ V'` such that each `f' j ≫ p` factors
through some `f (a j)`, then the `f i` form a pro-étale covering family of `V`. -/
lemma ofArrows_mem_proetalePrecoverage_of_comp {V V' : Scheme.{u}} (p : V' ⟶ V)
    [QuasiCompact p] [Surjective p] {ι : Type*} {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ V)
    (hf : ∀ i, WeaklyEtale (f i)) {κ : Type*} {Z' : κ → Scheme.{u}} (f' : ∀ j, Z' j ⟶ V')
    (a : κ → ι) (t : ∀ j, Z' j ⟶ Z (a j)) (w : ∀ j, t j ≫ f (a j) = f' j ≫ p)
    (h : Presieve.ofArrows Z' f' ∈ proetalePrecoverage V') :
    Presieve.ofArrows Z f ∈ proetalePrecoverage V := by
  let 𝒰 : PreZeroHypercover V := ⟨ι, Z, f⟩
  let 𝒰' : PreZeroHypercover V' := ⟨κ, Z', f'⟩
  have : QuasiCompactCover 𝒰' := presieve₀_mem_qcPrecoverage_iff.mp h.1
  have h₂ := (presieve₀_mem_precoverage_iff 𝒰').mp h.2
  refine ⟨presieve₀_mem_qcPrecoverage_iff (E := 𝒰).mpr ⟨fun {U} hU ↦ ?_⟩,
    (presieve₀_mem_precoverage_iff 𝒰).mpr ⟨fun v ↦ ?_, hf⟩⟩
  · obtain ⟨s, hs, W, hWc, hW⟩ := QuasiCompactCover.isCompactOpenCovered_of_isCompact 𝒰'
      (U := p ⁻¹ᵁ U) (p.isCompact_preimage hU.isCompact)
    refine IsCompactOpenCovered.of_comp (f := fun i ↦ (f i : Z i → V)) (fun j ↦ (f' j ≫ p))
      (a := a) (fun j ↦ (t j : Z' j → Z (a j))) (fun j ↦ (t j).continuous)
      (fun j ↦ funext fun z ↦ ?_) (fun i ↦ (f i).continuous) U.isOpen ⟨s, hs, W, hWc, ?_⟩
    · rw [Function.comp_apply, ← Scheme.Hom.comp_apply, w]
    · rw [← Set.image_preimage_eq (U : Set V) p.surjective, ← Scheme.Hom.coe_preimage, ← hW,
        Set.image_iUnion₂]
      simp_rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
      rfl
  · obtain ⟨x, rfl⟩ := p.surjective v
    obtain ⟨j, z, rfl⟩ := h₂.1 x
    exact ⟨a j, t j z, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩

namespace ProEt

/-- Base change along a quasi-compact surjective morphism `r : X ⟶ Y` reflects pro-étale
covering presieves: if the base change of a presieve `R` on `V : Y.ProEt` is a covering presieve,
then so is `R`. -/
lemma mem_precoverage_of_map_overPullback {X Y : Scheme.{u}} (r : X ⟶ Y) [QuasiCompact r]
    [Surjective r] {V : Y.ProEt} {R : Presieve V}
    (h : R.map (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r) ∈ precoverage X _) :
    R ∈ precoverage Y V := by
  obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
  rw [mem_precoverage_iff, Presieve.map_ofArrows] at h ⊢
  rw [Presieve.map_ofArrows] at h
  exact ofArrows_mem_proetalePrecoverage_of_comp (pullback.fst V.hom r) _
    (fun i ↦ weaklyEtale_left (f i)) _ id (fun i ↦ pullback.fst (Z i).hom r)
    (fun i ↦ (MorphismProperty.Over.isPullback_map_left r (f i)).w) h

variable {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r]

/-- Base change along a universal homeomorphism `r : X ⟶ Y` preserves and reflects covering
sieves of the pro-étale topologies. -/
theorem functorPushforward_overPullback_mem_topology_iff {V : Y.ProEt} (S : Sieve V) :
    S.functorPushforward (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r) ∈ topology X _ ↔
      S ∈ topology Y V := by
  refine ⟨fun h ↦ ?_, fun h ↦ (coverPreserving_overPullback r).cover_preserve h⟩
  obtain ⟨R', hR', hle⟩ := mem_topology_iff.mp h
  obtain ⟨κ, Z, g, rfl⟩ := R'.exists_eq_ofArrows
  choose W s k hs hk using fun j ↦ hle _ _ (Presieve.ofArrows.mk j)
  refine mem_topology_iff.mpr ⟨Presieve.ofArrows W s,
    mem_precoverage_of_map_overPullback r ?_, ?_⟩
  · rw [mem_precoverage_iff, Presieve.map_ofArrows, Presieve.map_ofArrows]
    rw [mem_precoverage_iff, Presieve.map_ofArrows] at hR'
    exact ofArrows_mem_proetalePrecoverage_of_comp (𝟙 _) _ (fun j ↦
      weaklyEtale_left ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map (s j))) _ id
      (fun j ↦ (k j).left) (fun j ↦ by simp [hk j]) hR'
  · rintro _ _ ⟨j⟩
    exact hs j

/-- Base change along a universal homeomorphism is locally faithful for the pro-étale
topologies: two morphisms with equal base changes are equalized by the equalizer inclusion,
whose base change is an isomorphism, so that it spans a covering sieve. -/
instance isLocallyFaithful_overPullback :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).IsLocallyFaithful (topology X) where
  functorPushforward_equalizer_mem {U V} f₁ f₂ he := by
    refine (functorPushforward_overPullback_mem_topology_iff r _).mpr (mem_topology_iff.mpr
      ⟨Presieve.singleton (equalizer.ι f₁ f₂),
        mem_precoverage_of_map_overPullback r ?_, ?_⟩)
    · rw [Presieve.map_singleton]
      have : IsIso ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).map
          (equalizer.ι f₁ f₂)) :=
        isIso_limit_cone_parallelPair_of_eq he
          (isLimitForkMapOfIsLimit _ _ (equalizerIsEqualizer f₁ f₂))
      exact Precoverage.HasIsos.mem_coverings_of_isIso _
    · rintro _ _ ⟨⟩
      exact equalizer.condition f₁ f₂

end ProEt

end AlgebraicGeometry.Scheme
