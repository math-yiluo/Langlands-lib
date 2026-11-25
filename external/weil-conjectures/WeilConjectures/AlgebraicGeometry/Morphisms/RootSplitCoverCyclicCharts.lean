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
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleRegularDivisorBaseChange

/-!
# Cyclic orbit charts for a cover split by a root extension

## References

* Stacks Project, Tag 0EYG, final paragraph on intermediate root extensions, and finite etale
  descent (Tags 02LA and 02VN)
* Stacks Project, Tag 0EYG, final paragraph
* Tags 02LA and 02VN, descent of finite and etale morphisms
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Covers split by a single root extension are locally unions of intermediate root covers. -/
theorem root_split_cover_cyclic_charts
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
    ∃ (S : CommRingCat.{u}) (ψ : Spec S ⟶ Spec R) (z : Spec S),
      Etale ψ ∧ ψ z = y ∧
      ∃ (m : ℕ) (h : S) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        IsRegularRing S ∧ IsSMulRegular S h ∧
        IsRegularRing (S ⧸ Ideal.span {h}) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)) h)
        ∃ γ : pullback p ψ ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p ψ := by
  dsimp
  intro δ hδ
  obtain ⟨S, φ, z, hφ, hz, m, e, he, γ, hγ⟩ :=
    root_split_cover_cyclic_chart_model R g n hn hg p hj d y δ hδ
  obtain ⟨hreg, hsmul, hquot⟩ := etale_regular_divisor_base_change R S φ g hg hφ
  exact ⟨S, Spec.map (CommRingCat.ofHom φ), z, hφ, hz,
    m, φ g, e, he, hreg, hsmul, hquot, γ, hγ⟩

end AlgebraicGeometry.Scheme
