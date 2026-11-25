/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

import WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicCharts

/-! Kummer charts for prime-to-residue-characteristic torsors on a regular divisor complement.

## References

* Stacks Project, Tags 09EB and 0EYG, including its case off the divisor
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The regular-divisor Kummer theorem, applied after an affine base change. -/
theorem GaloisCover.regular_divisor_punctured_root_chart
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (y : Spec R) :
    ∃ (S : CommRingCat.{u}) (ψ : Spec S ⟶ Spec R) (z : Spec S),
      Etale ψ ∧ ψ z = y ∧
      ∃ (m : ℕ) (g : S) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        IsRegularRing S ∧ IsSMulRegular S g ∧
        IsRegularRing (S ⧸ Ideal.span {g}) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C g)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C g))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C g)) g)
        ∃ γ : pullback (W.π ≫ i) (ψ ≫ φ) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd (W.π ≫ i) (ψ ≫ φ) := by
  obtain ⟨S, a, z, hψ, hz, n, hn, hS, hg, hSg, d, δ, hδ⟩ :=
    W.regular_divisor_root_splitting i G R φ f hG hf β hβ y
  let ψ := Spec.map a
  let g := a.hom f
  let p := pullback.snd (W.π ≫ i) (ψ ≫ φ)
  let t := pullback.lift
    (pullback.fst (W.π ≫ i) (ψ ≫ φ) ≫ W.π) (p ≫ ψ)
    (by simp only [Category.assoc]; exact pullback.condition)
  have ht : (t ≫ β.hom) ≫ Scheme.Opens.ι (X := Spec R)
      (PrimeSpectrum.basicOpen f) = p ≫ ψ := by
    simp only [Category.assoc, hβ, t, pullback.lift_snd]
  have hp : Set.range p ⊆ Set.range
      (Scheme.Opens.ι (X := Spec S) (PrimeSpectrum.basicOpen g)) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ψ (p x) ∈ PrimeSpectrum.basicOpen f
    have hx : ψ (p x) ∈ Set.range
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f)) := by
      refine ⟨(t ≫ β.hom) x, ?_⟩
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun k => k x) ht
    rw [Scheme.Opens.range_ι] at hx
    exact hx
  have hj : ∃ j : pullback (W.π ≫ i) (ψ ≫ φ) ⟶
      Scheme.Opens.toScheme (X := Spec S) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec S) (PrimeSpectrum.basicOpen g) = p :=
    ⟨IsOpenImmersion.lift _ p hp, IsOpenImmersion.lift_fac _ p hp⟩
  have : IsRegularRing S := hS
  have : IsRegularRing (S ⧸ Ideal.span {g}) := hSg
  obtain ⟨T, θ, w, hθ, hw, m, h, e, he, hT, hh, hTh, γ, hγ⟩ :=
    root_split_cover_cyclic_charts S g n hn hg
      (pullback.snd (W.π ≫ i) (ψ ≫ φ)) hj d z δ hδ
  have : Etale ψ := hψ
  have : Etale θ := hθ
  let ε := pullback.congrHom (rfl : W.π ≫ i = W.π ≫ i) (Category.assoc θ ψ φ)
  let α := (ε ≪≫ (pullbackLeftPullbackSndIso (W.π ≫ i) (ψ ≫ φ) θ).symm) ≪≫ γ
  refine ⟨T, θ ≫ ψ, w, inferInstance, ?_, m, h, e, he, hT, hh, hTh, α, ?_⟩
  · rw [Scheme.Hom.comp_apply, hw, hz]
  · simp only [α, Iso.trans_hom, Iso.symm_hom, Category.assoc, hγ,
      pullbackLeftPullbackSndIso_inv_snd_snd, ε, pullback.congrHom_hom,
      pullback.map, pullback.lift_snd, Category.comp_id]

end AlgebraicGeometry.Scheme
