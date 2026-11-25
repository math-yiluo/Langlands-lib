/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Etaleness of the punctured root cover

## References

* Stacks Project, Tag 0EYG, off-divisor branch
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The punctured root cover is etale over the original affine base. -/
theorem root_split_away_cover_etale
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R)) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    Etale (V.ι ≫ q) := by
  intro A N q V
  obtain ⟨u, hu⟩ := hn.2
  let f : Polynomial R := Polynomial.X ^ n - Polynomial.C g
  have hc : ∃ p₁ p₂ k, Polynomial.derivative f * p₁ + f * p₂ =
      (Polynomial.C g) ^ k := by
    refine ⟨Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.X, -1, 1, ?_⟩
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn.1)
    have hunit : Polynomial.C ((u⁻¹ : Rˣ) : R) * Polynomial.C (n : R) = 1 := by
      rw [← hu, ← Polynomial.C_mul]
      simp
    dsimp [f]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero, pow_one]
    rw [hm, Nat.succ_sub_one, pow_succ] at *
    linear_combination (Polynomial.X ^ (m + 1)) * hunit
  let P : StandardEtalePair R :=
    ⟨f, Polynomial.monic_X_pow_sub_C g (Nat.ne_of_gt hn.1), Polynomial.C g, hc⟩
  let S := Localization.Away (algebraMap R A g)
  have hS : Algebra.Etale R S := by
    have he : P.Ring ≃ₐ[R] S := by
      simpa [P, f, S, A, AdjoinRoot.mk_C] using P.equivAwayAdjoinRoot
    exact Algebra.Etale.of_equiv he
  have hspec : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr hS
  let e := basicOpenIsoSpecAway (R := CommRingCat.of A) (algebraMap R A g)
  have hcompat : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = V.ι ≫ q := by
    dsimp [e, q, S]
    rw [IsScalarTower.algebraMap_eq R A (Localization.Away (algebraMap R A g))]
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [← hcompat]
  infer_instance

end AlgebraicGeometry.Scheme
