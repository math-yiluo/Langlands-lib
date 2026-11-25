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
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.RingTheory.Henselian

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootOrbitDescent

/-! # Cyclic orbits on root-split strict local covers

## References

* Stacks Project, Tag 0EYG, local and intermediate-field paragraphs
* Tag 09EV, intermediate subextensions
* Stacks Project, Tag 0EYG, local and intermediate-field paragraphs, and Tag 09EV for intermediate
  subextensions
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem root_fixed_puncture_iso
    (H : CommRingCat.{u}) (B C : Type u) [CommRing B] [CommRing C]
    [Algebra H B] [Algebra H C] (h : H) (E : B ≃ₐ[H] C) :
    let NB := Spec (CommRingCat.of B)
    let NC := Spec (CommRingCat.of C)
    let UB : NB.Opens := PrimeSpectrum.basicOpen (algebraMap H B h)
    let UC : NC.Opens := PrimeSpectrum.basicOpen (algebraMap H C h)
    let qB := Spec.map (CommRingCat.ofHom (algebraMap H B))
    let qC := Spec.map (CommRingCat.ofHom (algebraMap H C))
    ∃ η : UB.toScheme ≅ UC.toScheme, η.hom ≫ UC.ι ≫ qC = UB.ι ≫ qB := by
  dsimp
  let f := (Scheme.Spec.mapIso E.symm.toRingEquiv.toCommRingCatIso.op).hom
  let UB : (Spec (CommRingCat.of B)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H B h)
  let UC : (Spec (CommRingCat.of C)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H C h)
  have hU : UB = f ⁻¹ᵁ UC := by
    apply TopologicalSpace.Opens.ext
    ext x
    change (algebraMap H B h ∉ x.asIdeal) ↔
      (E.symm (algebraMap H C h) ∉ x.asIdeal)
    rw [E.symm.commutes]
  let η := (Spec (CommRingCat.of B)).isoOfEq hU ≪≫ f.preimageIso UC
  refine ⟨η, ?_⟩
  have hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap H C)) =
      Spec.map (CommRingCat.ofHom (algebraMap H B)) := by
    dsimp [f]
    rw [← AlgebraicGeometry.Spec.map_comp]
    congr 1
    ext x
    exact E.symm.commutes x
  change η.hom ≫ UC.ι ≫ _ = UB.ι ≫ _
  simp only [η, Iso.trans_hom, Category.assoc, Hom.preimageIso_hom_ι_assoc]
  rw [hf, isoOfEq_hom_ι_assoc]

/-- Over a fixed regular strictly henselian local base, root-split finite etale
covers of a regular principal puncture decompose into intermediate root covers. -/
theorem root_split_strict_local_orbits
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
    ∃ (m : ℕ) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ e k ∣ n) ∧
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
  dsimp
  intro δ hδ
  obtain ⟨m, K, θ, hθ⟩ :=
    strict_local_root_orbit_descent R H g ι hg hgm n hn p j hj d δ hδ
  have hnH : 0 < n ∧ IsUnit (n : H) :=
    ⟨hn.1, by simpa only [map_natCast] using hn.2.map ι⟩
  have hc := fun k : Fin m ↦ strict_local_root_invariants H (ι g) n hnH (K k)
  let e : Fin m → ℕ := fun k ↦ (K k).index
  let B := ∀ k : Fin m, rootFixedAlgebra H (ι g) n (K k)
  let C := ∀ k : Fin m,
    AdjoinRoot ((Polynomial.X : Polynomial H) ^ e k - Polynomial.C (ι g))
  let E : B ≃ₐ[H] C := AlgEquiv.piCongrRight (fun k ↦ (hc k).2.2.some)
  obtain ⟨η, hη⟩ := root_fixed_puncture_iso H B C (ι g) E
  refine ⟨m, e, (fun k ↦ ⟨(hc k).1, (hc k).2.1⟩), θ ≪≫ η, ?_⟩
  rw [Iso.trans_hom, Category.assoc, hη, hθ]

end AlgebraicGeometry.Scheme
