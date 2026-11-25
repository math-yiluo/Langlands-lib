/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Affine localization of the punctured root cover

## References

* Stacks Project, Tag 0EYG, off-divisor branch
* Stacks Project, Tag 0EYG, affine localization construction
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The basic-open localization chart for the punctured root algebra. -/
theorem root_split_away_localization_chart
    (R : CommRingCat.{u}) (g : R) (n : ℕ) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∃ (S : CommRingCat.{u}) (φ : R →+* S) (e : Spec S ≅ V.toScheme),
      e.hom ≫ V.ι ≫ q = Spec.map (CommRingCat.ofHom φ) ∧ IsUnit (φ g) := by
  dsimp
  let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
  let h : A := algebraMap R A g
  let S : CommRingCat := CommRingCat.of (Localization.Away h)
  let φ : R →+* S := (algebraMap A (Localization.Away h)).comp (algebraMap R A)
  let V : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen h
  let e₀ := basicOpenIsoSpecAway (R := CommRingCat.of A) h
  let e : Spec S ≅ V.toScheme := e₀.symm
  refine ⟨S, φ, e, ?_, ?_⟩
  · have hb := basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) h
    change e₀.inv ≫ V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = _
    rw [← hb]
    simp [e₀, φ, h, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · dsimp [φ, h, S]
    exact IsLocalization.Away.algebraMap_isUnit h

end AlgebraicGeometry.Scheme
