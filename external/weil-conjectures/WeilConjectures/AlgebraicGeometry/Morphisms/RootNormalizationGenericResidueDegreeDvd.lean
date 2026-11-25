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
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Ideal

import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationResidueDegreeDvdCore
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkGaloisModel

/-! # Residue degrees of root normalization at the divisor generic point

## References

* Stacks Project, Tag 09EB (Galois DVR degree formula) and Tag 0307 (localization of integral
  closure)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- The normalization residue degree at the root divisor divides the torsor group order. -/
theorem root_normalization_generic_stalk_residue_degree_dvd
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R)
      (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R)
      (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (H : CommRingCat.{u}) [IsNoetherianRing H] (b : R ⟶ H)
    (hg : IsSMulRegular H (b.hom f))
    [IsDomain (H ⧸ Ideal.span {b.hom f})] :
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    (∀ (Q : Ideal A) (hQ : Q.IsPrime),
      letI := hQ
      AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g) ∈ Q →
        IsRegularLocalRing (Localization.AtPrime Q)) →
    ∀ (hN : IsLocallyNoetherian N),
    letI := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    letI := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∀ (x : a.normalization), a.fromNormalization x = j η →
        letI := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
        Module.finrank (N.residueField (a.fromNormalization x))
          (a.normalization.residueField x) ∣ Nat.card G := by
  dsimp only
  intro hroot hN hp hEtale hNorm D j hD hDi hj hcomp η hη x hx
  have hmodel := root_normalization_generic_stalk_galois_model i G W R φ f β hβ H b hg
  dsimp only at hmodel
  have hlocal := hmodel hroot hN hp hEtale hNorm D j hD hDi hj hcomp η hη x hx
  obtain ⟨S, T, alg, hlocal⟩ := hlocal
  let := alg
  obtain ⟨act, hlocal⟩ := hlocal
  let := act
  obtain ⟨hR, hS, hfinite, hflat, hgal, q₀, hq₀, hdegree⟩ := hlocal
  have := hR
  have := hS
  have := hfinite
  have := hflat
  have := hgal
  have := hq₀
  exact hdegree.symm ▸ normalization_residue_degree_dvd_core G T q₀

end AlgebraicGeometry.Scheme
