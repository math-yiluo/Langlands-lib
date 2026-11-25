/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # The generic fibre is the open pullback over a local trait

## References

* Stacks Project, Tag 0EYJ, reduction to the punctured local spectrum
* Stacks Project, Tag 0EYJ, local reduction and trait paragraphs
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Over the stalk trait at a minimal point outside U, the generic fibre is exactly C_U. -/
theorem stalk_generic_open_isPullback {S C : Scheme.{u}} [IsIntegral S]
    (c : C ⟶ S) (U : S.Opens) (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdvr : IsDiscreteValuationRing (S.presheaf.stalk s))
    (k : pullback (pullback.snd c (S.fromSpecStalk s))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (S.presheaf.stalk s) S.functionField))) ⟶ (c ⁻¹ᵁ U).toScheme)
    (hk : k ≫ (c ⁻¹ᵁ U).ι =
      pullback.fst _ _ ≫ pullback.fst c (S.fromSpecStalk s)) :
    IsPullback k (pullback.fst _ _) (c ⁻¹ᵁ U).ι
      (pullback.fst c (S.fromSpecStalk s)) := by
  let R := S.presheaf.stalk s
  let K := S.functionField
  let a := S.fromSpecStalk s
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let d := pullback.snd c a
  let g := pullback.fst c a
  let p := pullback.fst d b
  have : IsDiscreteValuationRing R := hdvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hle : Submonoid.powers ϖ ≤ nonZeroDivisors R := by
    rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hϖ.ne_zero)
  have hdvd : ∀ x ∈ nonZeroDivisors R, ∃ y ∈ Submonoid.powers ϖ, x ∣ y := by
    intro x hx
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hx) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  have : IsLocalization.Away ϖ K :=
    (IsLocalization.iff_of_le_of_exists_dvd (S := K) (Submonoid.powers ϖ)
      (nonZeroDivisors R) hle hdvd).mpr
      inferInstance
  have : IsOpenImmersion b := IsOpenImmersion.of_isLocalization ϖ
  have hb : b.opensRange = PrimeSpectrum.basicOpen ϖ := by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range K ϖ
  have hclosed : ∀ x : Spec R, ϖ ∈ x.asIdeal ↔ x = IsLocalRing.closedPoint R := by
    intro x
    constructor
    · intro hx
      apply PrimeSpectrum.ext
      exact (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le x.isPrime.ne_top
        (by rw [hϖ.maximalIdeal_eq]; exact Ideal.span_le.mpr (by simpa using hx)) |>.symm
    · rintro rfl
      change ϖ ∈ IsLocalRing.maximalIdeal R
      rw [hϖ.maximalIdeal_eq]
      exact Ideal.subset_span (Set.mem_singleton ϖ)
  have hbase : a ⁻¹ᵁ U = b.opensRange := by
    rw [hb]
    ext x
    change a x ∈ U ↔ ϖ ∉ x.asIdeal
    rw [hclosed]
    constructor
    · intro hx he
      subst x
      apply hs
      change (S.fromSpecStalk s) (IsLocalRing.closedPoint (S.presheaf.stalk s)) ∈ U at hx
      rwa [fromSpecStalk_closedPoint] at hx
    · intro hx
      by_contra hn
      have hspec : a x ⤳ s := by
        exact ((IsLocalRing.specializes_closedPoint x).map a.continuous).trans
          (specializes_of_eq fromSpecStalk_closedPoint)
      have he : a x = a (IsLocalRing.closedPoint R) := by
        change a x = (S.fromSpecStalk s) (IsLocalRing.closedPoint (S.presheaf.stalk s))
        rw [fromSpecStalk_closedPoint]
        exact hmin (a x) hspec hn
      exact hx (a.isEmbedding.injective he)
  have : IsOpenImmersion p := by dsimp [p]; infer_instance
  apply IsOpenImmersion.isPullback k p (c ⁻¹ᵁ U).ι g hk.symm
  change g ⁻¹ᵁ (c ⁻¹ᵁ U).ι.opensRange = p.opensRange
  rw [Scheme.Opens.opensRange_ι, Hom.opensRange_pullbackFst, ← hbase,
    ← Hom.comp_preimage, ← Hom.comp_preimage, pullback.condition]

end AlgebraicGeometry.Scheme
