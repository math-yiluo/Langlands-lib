/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot

import WeilConjectures.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorRootModelNormal

/-!
# Normal root models containing a generic trait torsor as a dense open

## References

* Stacks Project, Tag 0EYJ, trait paragraph
* Tags 09EB, 0EYG and 0EYH
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A tame generic torsor admits local normal integral root models before normalization. -/
theorem GaloisCover.trait_generic_root_model
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Scheme.{u}} (d : L ⟶ Spec (CommRingCat.of A))
    [QuasiCompact d] [QuasiSeparated d] [Smooth d]
    (G : Type (u + 1)) [Group G] [Finite G] (hG : IsUnit (Nat.card G : A))
    (W : GaloisCover G (pullback d (Spec.map (CommRingCat.ofHom (algebraMap A K))))) :
    letI : IsFinite W.π := W.isFinite
    let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
    let p := W.π ≫ pullback.fst d b
    ∀ x : L, ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R),
      Etale φ ∧ φ y = x ∧
      ∃ (m : ℕ) (f : R) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : R)) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap R (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))))
        (∀ z : N, IsDomain (N.presheaf.stalk z) ∧
          IsIntegrallyClosed (N.presheaf.stalk z)) ∧
        ∃ V : N.Opens, Dense (V : Set N) ∧
          ∃ γ : pullback p φ ≅ V.toScheme,
            γ.hom ≫ V.ι ≫ q = pullback.snd p φ := by
  dsimp only
  intro x
  obtain ⟨R, φ, y, hφ, hy, m, f, e, he, hR, hf, hRf, γ, hγ⟩ :=
    GaloisCover.trait_generic_punctured_root_chart A K d G hG W x
  have : IsRegularRing R := hR
  have : IsRegularRing (R ⧸ Ideal.span {f}) := hRf
  refine ⟨R, φ, y, hφ, hy, m, f, e, he, ?_, ?_⟩
  · exact regular_divisor_root_model_normal R m f hf e he
  · let B := ∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)
    let V : (Spec (CommRingCat.of B)).Opens :=
      PrimeSpectrum.basicOpen (algebraMap R B f)
    refine ⟨V, ?_, γ, hγ⟩
    have (k : Fin m) : Module.Free R
        (AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)) :=
      (Polynomial.monic_X_pow_sub_C f (he k).1.ne').free_adjoinRoot
    have hfB : IsSMulRegular B (algebraMap R B f) := hf.of_flat
    have hr : IsRegular (algebraMap R B f) :=
      (Commute.isRegular_iff (fun b ↦ Commute.all _ b)).mpr
        (isLeftRegular_iff.mpr hfB)
    have hinj : Function.Injective
        (algebraMap B (Localization.Away (algebraMap R B f))) :=
      IsLocalization.injective (M := Submonoid.powers (algebraMap R B f))
        (Localization.Away (algebraMap R B f)) (by
        rintro a ⟨n, rfl⟩
        exact (hr.pow n).mem_nonZeroDivisors)
    change Dense (↑(PrimeSpectrum.basicOpen (algebraMap R B f)) : Set (PrimeSpectrum B))
    rw [← PrimeSpectrum.localization_away_comap_range
      (Localization.Away (algebraMap R B f)) (algebraMap R B f)]
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le


end AlgebraicGeometry.Scheme
