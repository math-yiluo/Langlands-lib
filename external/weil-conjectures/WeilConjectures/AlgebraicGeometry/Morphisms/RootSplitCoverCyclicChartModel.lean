/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverOnDivisorCharts
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts

/-!
# Cyclic orbit charts for a cover split by a root extension

## References

* Stacks Project, Tag 0EYG, final paragraph on intermediate root extensions, and finite etale
  descent (Tags 02LA and 02VN)
* Stacks Project, Tag 0EYG, final intermediate-root-extension paragraph
* Tags 02LA, 02VN, 0BSK and 05N9
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Cyclic descent gives a root chart with equation the image of the original divisor. -/
theorem root_split_cover_cyclic_chart_model
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    [IsRegularRing R] (hg : IsSMulRegular R g)
    [IsRegularRing (R ⧸ Ideal.span {g})]
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (hj : ∃ j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) (y : Spec R) :
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
      ∃ (m : ℕ) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C (φ g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C (φ g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C (φ g))) (φ g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom φ)) := by
  classical
  dsimp
  intro δ hδ
  by_cases hy : g ∈ y.asIdeal
  · obtain ⟨S, ψ, z, hψ, hz, m, e, he, γ, hγ⟩ :=
      root_split_cover_on_divisor_charts R g n hn hg p hj d y hy δ hδ
    refine ⟨S, ψ, z, hψ, hz, m, e, he, γ, hγ⟩
  · obtain ⟨S, φ, z, hφ, hz, hunit, γ, hγ⟩ :=
      root_split_cover_away_divisor_charts R g n hn p d y hy δ hδ
    refine ⟨S, φ, z, hφ, hz, d, fun _ ↦ 1, ?_, γ, hγ⟩
    intro k
    exact ⟨Nat.zero_lt_one, by simp⟩

end AlgebraicGeometry.Scheme
