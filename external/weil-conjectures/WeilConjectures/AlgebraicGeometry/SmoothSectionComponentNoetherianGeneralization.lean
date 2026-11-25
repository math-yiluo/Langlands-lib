/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.NoetherianSpecializationTrait
import WeilConjectures.AlgebraicGeometry.SectionComponentPullback
import WeilConjectures.AlgebraicGeometry.SmoothTraitSectionComponents

/-!
# Generalization of a smooth section component over a noetherian base

Source: Stacks Project, Tag 055Q.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The noetherian geometric argument produces an open stable locus agreeing with the
section component locus.
(blueprint: lem-sbc-smooth-section-component-noetherian-generalization-core) -/
theorem Smooth.exists_noetherian_section_component_stable_locus {P T : Scheme.{u}}
    (g : P ⟶ T) [Smooth g] [QuasiCompact g] [QuasiSeparated g]
    [IsNoetherian T]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    ∃ U : Set P, (∀ p, p ∈ U ↔ p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))) ∧
      StableUnderGeneralization U := by
  refine ⟨{p | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))},
    fun _ ↦ Iff.rfl, ?_⟩
  intro x y hxy hx
  change x ∈ connectedComponentIn (g ⁻¹' {g x}) (σ (g x)) at hx
  change y ∈ connectedComponentIn (g ⁻¹' {g y}) (σ (g y))
  by_cases hne : y = x
  · simpa [hne] using hx
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨R, hR, hdom, hdvr, a, ha₀, haη⟩ := exists_trait_of_strict_specializes hxy hne
  let b := a ≫ g
  let q := Limits.pullback.snd g b
  let σ' : Spec (.of R) ⟶ Limits.pullback g b :=
    Limits.pullback.lift (b ≫ σ) (𝟙 _) (by simp [hσ])
  let τ : Spec (.of R) ⟶ Limits.pullback g b :=
    Limits.pullback.lift a (𝟙 _) (by simp [b])
  have hσ' : σ' ≫ q = 𝟙 _ :=
    Limits.pullback.lift_snd _ _ _
  have hτ : τ ≫ q = 𝟙 _ := Limits.pullback.lift_snd _ _ _
  have hτq (t : Spec (.of R)) : q (τ t) = t := by
    rw [← Scheme.Hom.comp_apply, hτ]
    rfl
  have hτfst (t : Spec (.of R)) : Limits.pullback.fst g b (τ t) = a t := by
    rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst]
  have hσfst (t : Spec (.of R)) : Limits.pullback.fst g b (σ' t) = σ (b t) := by
    rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst, Scheme.Hom.comp_apply]
  have hclosed : τ (IsLocalRing.closedPoint R) ∈
    connectedComponentIn (q ⁻¹' {IsLocalRing.closedPoint R})
        (σ' (IsLocalRing.closedPoint R)) := by
    have hbaseChange := section_component_preimage_of_isPullback g σ hσ
      (Limits.pullback.fst g b) q b (IsPullback.of_hasPullback g b)
      σ' hσ' (Limits.pullback.lift_fst _ _ _)
    have h := (Set.ext_iff.mp hbaseChange (τ (IsLocalRing.closedPoint R))).mp
      (by simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hτfst, ha₀] using hx)
    change τ (IsLocalRing.closedPoint R) ∈
      connectedComponentIn (q ⁻¹' {q (τ (IsLocalRing.closedPoint R))})
        (σ' (q (τ (IsLocalRing.closedPoint R)))) at h
    simpa only [hτq] using h
  have hgeneric := Smooth.trait_sections_mem_same_generic_component q σ' τ hσ' hτ hclosed
  let η : Spec (.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hσmem : σ' η ∈ q ⁻¹' {η} := by
    change q (σ' η) = η
    rw [← Scheme.Hom.comp_apply, hσ']
    rfl
  have himage := (Limits.pullback.fst g b).continuous.continuousOn.image_connectedComponentIn_subset
    hσmem ⟨τ η, hgeneric, hτfst η⟩
  have hfibre : Limits.pullback.fst g b '' (q ⁻¹' {η}) ⊆ g ⁻¹' {g y} := by
    rintro _ ⟨z, hz, rfl⟩
    change q z = η at hz
    change g (Limits.pullback.fst g b z) = g y
    rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
    change b (q z) = g y
    rw [hz]
    change g (a η) = g y
    rw [haη]
  have hbase : Limits.pullback.fst g b (σ' η) = σ (g y) := by
    rw [hσfst]
    change σ (g (a η)) = σ (g y)
    rw [haη]
  have h := connectedComponentIn_mono (Limits.pullback.fst g b (σ' η)) hfibre himage
  simpa only [η, haη, hbase] using h

/-- (blueprint: lem-sbc-smooth-section-component-noetherian-generalization) -/
theorem Smooth.section_component_generalization_of_isNoetherian {P T : Scheme.{u}}
    (g : P ⟶ T) [Smooth g] [QuasiCompact g] [QuasiSeparated g] [IsNoetherian T]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) {x y : P} (hxy : y ⤳ x)
    (hx : x ∈ connectedComponentIn (g ⁻¹' {g x}) (σ (g x))) :
    y ∈ connectedComponentIn (g ⁻¹' {g y}) (σ (g y)) := by
  obtain ⟨U, hU, hstable⟩ := Smooth.exists_noetherian_section_component_stable_locus g σ hσ
  apply (hU y).mp
  apply hstable hxy
  exact (hU x).mpr hx

end AlgebraicGeometry
