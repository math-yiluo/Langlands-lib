/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Algebra.Pi
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayLocalizationPoint
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayTransportChart

/-!
# Degree-one root charts away from the divisor

## References

* Stacks Project, Tag 0EYG, first paragraph of the proof (the point off the divisor), and Tags 02LA,
  02VN and 04HN
* Stacks Project, Tag 0EYG, first proof paragraph
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A root-split cover has only degree-one charts near a point off the divisor. -/
theorem root_split_cover_away_divisor_charts
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (d : ℕ) (y : Spec R) (hy : g ∉ y.asIdeal) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ (S : CommRingCat.{u}) (φ : R →+* S) (z : Spec S),
      Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      (Spec.map (CommRingCat.ofHom φ)) z = y ∧
      IsUnit (φ g) ∧
        let N := Spec (CommRingCat.of (Fin d →
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (Fin d →
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (Fin d →
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))) (φ g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom φ)) := by
  dsimp
  intro δ hδ
  obtain ⟨S, φ, z, e, he, hφ, hz, hunit⟩ :=
    root_split_away_localization_point R g n hn y hy
  obtain ⟨γ, hγ⟩ := root_split_away_transport_chart R g n p d S φ hunit e he δ hδ
  exact ⟨S, φ, z, hφ, hz, hunit, γ, hγ⟩

end AlgebraicGeometry.Scheme
