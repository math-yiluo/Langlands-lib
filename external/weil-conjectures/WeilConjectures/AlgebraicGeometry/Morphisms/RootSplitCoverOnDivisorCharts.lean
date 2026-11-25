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

import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootChartsIndEtaleDescent

/-! # Cyclic root charts near the regular divisor

## References

* Stacks Project, Tag 0EYG, strict henselization and intermediate-root paragraphs
* Stacks Project, Tags 02LA, 02VN and 05N9 (descent)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Cyclic root charts near a point on the regular divisor: if the pullback of the punctured
root cover along `p` splits, then a point `y ∈ V(g)` has an étale neighbourhood `Spec S` over
which the pullback of `p` is the punctured spectrum of a finite product of root algebras of
degrees invertible in `S`. -/
theorem root_split_cover_on_divisor_charts
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    [IsRegularRing R] (hg : IsSMulRegular R g)
    [IsRegularRing (R ⧸ Ideal.span {g})]
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (hj : ∃ j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) (y : Spec R) (hy : g ∈ y.asIdeal) :
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
  dsimp only
  intro δ hδ
  obtain ⟨hp, H, ι, x, hι, hx, m, e, he, γ, hγ⟩ :=
    root_split_cover_indEtale_charts R g n hn hg p hj d y hy δ hδ
  obtain ⟨S, φ, z, hφ, hz, heS, γS, hγS⟩ :=
    punctured_root_charts_descend_indEtale R H g ι hι p hp x y hx m e he ⟨γ, hγ⟩
  exact ⟨S, φ, z, hφ, hz, m, e, heS, γS, hγS⟩

end AlgebraicGeometry.Scheme
