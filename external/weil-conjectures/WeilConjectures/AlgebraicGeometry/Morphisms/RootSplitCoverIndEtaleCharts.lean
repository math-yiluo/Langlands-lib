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

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.RingTheory.ProEtale.IndEtale

import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitFactorFiniteEtale
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitStrictLocalOrbits

/-! # Cyclic root charts over the strict local limit

## References

* Stacks Project, Tag 0EYG, strict henselization and intermediate-root paragraphs
* Tags 02LA and 02VN for descent from the punctured root cover
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The affine finite-presentation cover has a cyclic root model over an ind-etale local limit.
-/
theorem root_split_cover_indEtale_charts
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
    (IsAffineHom p ∧ LocallyOfFinitePresentation p) ∧
    ∃ (H : CommRingCat.{u}) (ι : R →+* H) (x : Spec H),
      ι.IndEtale ∧
      (Spec.map (CommRingCat.ofHom ι)) x = y ∧
      ∃ (m : ℕ) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : H)) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap H (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap H (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g))) (ι g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by
  dsimp only
  intro δ hδ
  obtain ⟨j, hj⟩ := hj
  obtain ⟨hjFinite, hjEtale⟩ :=
    root_split_factor_finite_etale R g n hn p j hj d δ hδ
  have : IsFinite j := hjFinite
  have : Etale j := hjEtale
  have hbasic : IsAffineHom
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g)) := by
    rw [← basicOpen_eq_of_affine g]
    infer_instance
  have : IsAffineHom
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g)) := hbasic
  have hp : IsAffineHom p ∧ LocallyOfFinitePresentation p := by
    rw [← hj]
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨H, ι, hι, hH, hreg, hquot, hgH, hgm, x, hx⟩ :=
    regular_divisor_strict_local_limit R g hg y hy
  have : IsStrictlyHenselianLocalRing H := hH
  have : IsRegularLocalRing H := hreg
  have : IsRegularLocalRing (H ⧸ Ideal.span {ι g}) := hquot
  obtain ⟨m, e, he, γ, hγ⟩ :=
    root_split_strict_local_orbits R H g ι hgH hgm n hn p j hj d δ hδ
  have hnH : IsUnit (n : H) := by
    simpa only [map_natCast] using hn.2.map ι
  have heUnit : ∀ k, 0 < e k ∧ IsUnit (e k : H) := by
    intro k
    obtain ⟨a, ha⟩ := (he k).2
    have hdvd : (e k : H) ∣ (n : H) := by
      refine ⟨(a : H), ?_⟩
      simpa only [Nat.cast_mul] using congrArg (fun t : ℕ ↦ (t : H)) ha
    exact ⟨(he k).1, isUnit_of_dvd_unit hdvd hnH⟩
  exact ⟨hp, H, ι, x, hι, hx, m, e, heUnit, γ, hγ⟩

end AlgebraicGeometry.Scheme
