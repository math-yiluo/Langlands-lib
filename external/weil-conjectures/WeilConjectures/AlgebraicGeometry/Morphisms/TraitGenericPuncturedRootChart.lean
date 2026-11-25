/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothTraitAffineGenericOpen
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import Mathlib.RingTheory.TensorProduct.Quotient

/-! Punctured Kummer charts before normality.

## References

* Stacks Project, Tags 0EYJ (first trait paragraph), 09EB and 0EYG
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem smooth_trait_regular_quotient
    (A R : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [Algebra A R] [Algebra.Smooth A R]
    (π : A) (hπ : Irreducible π) :
    IsRegularRing R ∧ IsSMulRegular R (algebraMap A R π) ∧
      IsRegularRing (R ⧸ Ideal.span {algebraMap A R π}) := by
  have hR : IsRegularRing R := Algebra.isRegularRing_of_smooth A R
  have hπreg : IsSMulRegular A π :=
    isLeftRegular_iff.mp (IsRegular.of_ne_zero' hπ.ne_zero).1
  have hf : IsSMulRegular R (algebraMap A R π) := hπreg.of_flat
  refine ⟨hR, hf, ?_⟩
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let k := A ⧸ I
  let : Field k := Ideal.Quotient.field I
  have hT : IsRegularRing (TensorProduct A k R) :=
    Algebra.isRegularRing_of_smooth k (TensorProduct A k R)
  have hQ : IsRegularRing (R ⧸ I.map (algebraMap A R)) :=
    IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).symm.toRingEquiv
  rw [show I = Ideal.span {π} from hπ.maximalIdeal_eq] at hQ
  rw [Ideal.map_span] at hQ
  rw [Set.image_singleton] at hQ
  exact hQ

/-- Punctured Kummer charts for a generic torsor over a smooth trait family. -/
theorem GaloisCover.trait_generic_punctured_root_chart
    (A K : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Scheme.{u}} (d : L ⟶ Spec (CommRingCat.of A))
    [QuasiCompact d] [QuasiSeparated d] [Smooth d]
    (G : Type (u + 1)) [Group G] [Finite G] (hG : IsUnit (Nat.card G : A))
    (W : GaloisCover G (pullback d (Spec.map (CommRingCat.ofHom (algebraMap A K))))) :
    letI : IsFinite W.π := W.isFinite
    let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
    let p := W.π ≫ pullback.fst d b
    ∀ x : L, ∃ (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (y : Spec R),
      Etale φ ∧ φ y = x ∧
      ∃ (m : ℕ) (f : R) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : R)) ∧
        IsRegularRing R ∧ IsSMulRegular R f ∧
        IsRegularRing (R ⧸ Ideal.span {f}) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap R (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap R (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)) f)
        ∃ γ : pullback p φ ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p φ := by
  dsimp only
  intro x
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨R, φ, y, hφ, hy, a, hsmooth, β, hβ⟩ :=
    smooth_trait_affine_generic_open A K π hπ d x
  let : Algebra A R := a
  have : Algebra.Smooth A R := hsmooth
  obtain ⟨hR, hf, hRf⟩ := smooth_trait_regular_quotient A R π hπ
  have : IsRegularRing R := hR
  have : IsRegularRing (R ⧸ Ideal.span {algebraMap A R π}) := hRf
  have hGR : IsUnit (Nat.card G : R) := by
    simpa only [map_natCast] using hG.map (algebraMap A R)
  obtain ⟨S, ψ, z, hψ, hz, m, g, e, he, hS, hg, hSg, γ, hγ⟩ :=
    GaloisCover.regular_divisor_punctured_root_chart
      (pullback.fst d (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      G W R φ (algebraMap A R π) hGR hf β hβ y
  have : Etale φ := hφ
  have : Etale ψ := hψ
  refine ⟨S, ψ ≫ φ, z, inferInstance, ?_, m, g, e, he, hS, hg, hSg, γ, hγ⟩
  rw [Scheme.Hom.comp_apply, hz, hy]

end AlgebraicGeometry.Scheme
