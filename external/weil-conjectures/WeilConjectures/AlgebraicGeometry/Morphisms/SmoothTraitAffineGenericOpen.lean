/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! Affine neighborhoods and the principal generic open of a smooth trait family.

## References

* Stacks Project, Tag 0EYJ, first paragraph of the proof
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem fractionRing_away_uniformizer
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨s, n, rfl⟩
    apply Ne.isUnit
    simpa only [map_zero] using
      (IsFractionRing.injective A K).ne (pow_ne_zero n hπ.ne_zero)
  · intro z
    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) z
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp s.property) hπ
    refine ⟨(r * ↑v⁻¹, ⟨π ^ n, n, rfl⟩), ?_⟩
    have hvK : algebraMap A K (v : A) ≠ 0 :=
      (v.isUnit.map (algebraMap A K)).ne_zero
    change z * algebraMap A K (π ^ n) = algebraMap A K (r * ↑v⁻¹)
    rw [map_mul]
    apply mul_right_cancel₀ hvK
    calc
      (z * algebraMap A K (π ^ n)) * algebraMap A K ↑v =
          z * algebraMap A K (s : A) := by rw [hv, map_mul]; ring
      _ = algebraMap A K r := hs
      _ = (algebraMap A K r * algebraMap A K ↑v⁻¹) * algebraMap A K ↑v := by
        rw [mul_assoc, ← map_mul]
        simp
  · intro x y hxy
    exact ⟨1, by simpa using (IsFractionRing.injective A K) hxy⟩

/-- An affine smooth trait neighborhood identifies its generic fibre with the principal
open of the image of a specified uniformizer. -/
theorem smooth_trait_affine_generic_open
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π)
    {L : Scheme.{u}} (d : L ⟶ Spec (CommRingCat.of A)) [Smooth d] (x : L) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
    ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R),
      Etale φ ∧ φ y = x ∧
      ∃ _a : Algebra A R, Algebra.Smooth A R ∧
        let D : (Spec R).Opens := PrimeSpectrum.basicOpen (algebraMap A R π)
        ∃ β : pullback (pullback.fst d b) φ ≅ D.toScheme,
          β.hom ≫ D.ι = pullback.snd (pullback.fst d b) φ := by
  have : IsLocalization.Away π K := fractionRing_away_uniformizer A K π hπ
  let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have : IsOpenImmersion b := IsOpenImmersion.of_isLocalization π
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  let R := Γ(L, V)
  let φ : Spec R ⟶ L := hV.fromSpec
  let y : Spec R := hV.isoSpec.hom ⟨x, hxV⟩
  have hy : φ y = x := by
    change (hV.isoSpec.hom ≫ hV.fromSpec) ⟨x, hxV⟩ = x
    simp
  let a := (Spec.preimage (φ ≫ d)).hom.toAlgebra
  let : Algebra A R := a
  have hsmooth : Algebra.Smooth A R := by
    apply RingHom.Smooth.toAlgebra
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    rw [Spec.map_preimage]
    infer_instance
  refine ⟨R, φ, y, inferInstance, hy, a, hsmooth, ?_⟩
  let D : (Spec R).Opens := PrimeSpectrum.basicOpen (algebraMap A R π)
  have hrange : Set.range (pullback.snd (pullback.fst d b) φ) = (D : Set (Spec R)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    rw [Scheme.Hom.opensRange_pullbackFst]
    change (φ ≫ d) ⁻¹' Set.range b = (D : Set (Spec R))
    rw [show Set.range b = (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum A)) from
      PrimeSpectrum.localization_away_comap_range K π]
    rw [← Spec.map_preimage (φ ≫ d)]
    exact congrArg (fun O : (Spec R).Opens ↦ (O : Set (Spec R)))
      (PrimeSpectrum.comap_basicOpen (Spec.preimage (φ ≫ d)).hom π)
  let β : pullback (pullback.fst d b) φ ≅ D.toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.snd (pullback.fst d b) φ) D.ι
      (hrange.trans (Scheme.Opens.range_ι D).symm)
  exact ⟨β, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

end AlgebraicGeometry.Scheme
