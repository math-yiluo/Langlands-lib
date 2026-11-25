/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.RingTheory.Henselian

import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootTorsorProperties
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Descent of a root-split cover to fixed subalgebras

## References

* Stacks Project, Tag 0EYG, local and intermediate-field paragraphs
* Tag 09EV, intermediate subextensions
* Stacks Project, Tag 0EYG, strict local and normal-domain paragraphs
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Root-split covers descend to products of fixed subalgebras of the root algebra. -/
theorem strict_local_root_orbit_descent
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    [IsStrictlyHenselianLocalRing H] [IsRegularLocalRing H]
    [IsRegularLocalRing (H ⧸ Ideal.span {ι g})]
    (hg : IsSMulRegular H (ι g)) (hgm : ι g ∈ IsLocalRing.maximalIdeal H)
    (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    [IsFinite j] [Etale j] (d : ℕ) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ (m : ℕ) (K : Fin m → Subgroup (rootsOfUnity n H)),
        let B := ∀ k : Fin m, rootFixedAlgebra H (ι g) n (K k)
        let N := Spec (CommRingCat.of B)
        let q := Spec.map (CommRingCat.ofHom (algebraMap H B))
        let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
        ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
          θ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by
  classical
  dsimp only
  let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
  let C := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C (ι g))
  let qR := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let VR : (Spec (CommRingCat.of A)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap R A g)
  let qH := Spec.map (CommRingCat.ofHom (algebraMap H C))
  let VH : (Spec (CommRingCat.of C)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H C (ι g))
  intro δ hδ
  have hnH : 0 < n ∧ IsUnit (n : H) :=
    ⟨hn.1, by simpa using hn.2.map ι⟩
  obtain ⟨hdom, het, hfiber⟩ :=
    strict_local_root_torsor_properties H (ι g) hg hgm n hnH
  have : IsDomain C := hdom
  have : NeZero n := ⟨hn.1.ne'⟩
  have hmonic : ((Polynomial.X : Polynomial H) ^ n - Polynomial.C (ι g)).Monic :=
    Polynomial.monic_X_pow_sub_C (ι g) hn.1.ne'
  have hdeg : ((Polynomial.X : Polynomial H) ^ n - Polynomial.C (ι g)).degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C hn.1]
    exact_mod_cast hn.1.ne'
  have : Module.Finite H C := hmonic.finite_adjoinRoot
  have : Module.FaithfullyFlat H C := AdjoinRoot.faithfullyFlat_of_monic hmonic hdeg
  have hh : ι g ≠ 0 := by
    intro h
    have h01 : (0 : H) = 1 := hg (by simp [h])
    exact zero_ne_one h01
  have hne : algebraMap H C (ι g) ≠ 0 := by
    exact fun h ↦ hh (AdjoinRoot.of.injective_of_degree_ne_zero hdeg
      (h.trans (map_zero _).symm))
  have hone : rootRotation H (ι g) n 1 = AlgHom.id H C := by
    apply AdjoinRoot.algHom_ext
    simp [rootRotation, AdjoinRoot.liftAlgHom_root]
    rfl
  have hmul (a b : rootsOfUnity n H) :
      rootRotation H (ι g) n (a * b) =
        (rootRotation H (ι g) n a).comp (rootRotation H (ι g) n b) := by
    apply AdjoinRoot.algHom_ext
    simp only [rootRotation, AdjoinRoot.liftAlgHom_root, AlgHom.comp_apply,
      map_mul, AlgHom.commutes, Subgroup.coe_mul, Units.val_mul]
    ring
  have hroot : AdjoinRoot.root
      ((Polynomial.X : Polynomial H) ^ n - Polynomial.C (ι g)) ^ n =
        algebraMap H C (ι g) := by
    have h := AdjoinRoot.eval₂_root
      ((Polynomial.X : Polynomial H) ^ n - Polynomial.C (ι g))
    simpa [sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using h
  let φ : A →+* C := AdjoinRoot.lift ((algebraMap H C).comp ι)
    (AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ n - Polynomial.C (ι g))) (by
      simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, RingHom.comp_apply, sub_eq_zero] using hroot)
  have hφ (r : R) : φ (algebraMap R A r) = algebraMap H C (ι r) :=
    AdjoinRoot.lift_of _
  let f := Spec.map (CommRingCat.ofHom φ)
  have hpre : VH ≤ f ⁻¹ᵁ VR := by
    change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
      Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ PrimeSpectrum.basicOpen (algebraMap R A g)
    rw [SpecMap_preimage_basicOpen, CommRingCat.ofHom_apply, hφ]
  let k : VH.toScheme ⟶ VR.toScheme := f.resLE VR VH hpre
  have hbase : f ≫ qR = qH ≫ Spec.map (CommRingCat.ofHom ι) := by
    dsimp [f, qR, qH]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hφ r
  have hk : k ≫ (VR.ι ≫ qR) =
      VH.ι ≫ qH ≫ Spec.map (CommRingCat.ofHom ι) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hbase]
  obtain ⟨m, K, θ, hθ⟩ := affine_torsor_fixed_puncture_descent
    R H g ι C (rootsOfUnity n H) (rootRotation H (ι g) n) hone hmul hne
    p j hj het hfiber VR.toScheme (VR.ι ≫ qR) k hk d δ hδ
  exact ⟨m, K, θ, hθ⟩

end AlgebraicGeometry.Scheme
