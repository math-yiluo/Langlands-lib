/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore

/-! # Descent along a connected affine torsor on a principal open

## References

* Stacks Project, Tag 0EYG, normal-domain and intermediate-field paragraphs
* Tag 03SF, Galois covers and their quotients
* Stacks Project, Tag 03SF (quotients of Galois covers), and Tag 0EYG (normal-domain and
  intermediate-field paragraphs)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A split cover descends along a connected affine torsor to fixed-ring punctures. -/
theorem affine_torsor_fixed_puncture_descent
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    [IsFinite j] [Etale j] :
    let q := Spec.map (CommRingCat.ofHom (algebraMap H C))
    let V : (Spec (CommRingCat.of C)).Opens :=
      PrimeSpectrum.basicOpen (algebraMap H C (ι g))
    Etale (V.ι ≫ q) →
    (∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b) →
    ∀ (T : Scheme.{u}) (t : T ⟶ Spec R) (k : V.toScheme ⟶ T),
      k ≫ t = V.ι ≫ q ≫ Spec.map (CommRingCat.ofHom ι) →
    ∀ (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t →
    ∃ (m : ℕ) (K : Fin m → Subgroup G),
      let B := ∀ k : Fin m,
        (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
      let N := Spec (CommRingCat.of B)
      let q := Spec.map (CommRingCat.ofHom (algebraMap H B))
      let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
      ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
        θ.hom ≫ V.ι ≫ q =
        pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by
  dsimp
  intro hEt hrot T t k hk d δ hδ
  obtain ⟨m, K, _hmd, θ, hθ⟩ := affine_torsor_fixed_orbits
    R H g ι C G ρ hρone hρmul hne p j hj d hEt hrot T t k hk δ hδ
  exact ⟨m, K, θ, hθ⟩

end AlgebraicGeometry.Scheme
