/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.Mathlib.RingTheory.TotallySplit

/-! # Etaleness of an invariant principal open of an affine torsor

## References

* Stacks Project, Tag 03SF, finite Galois covers and permutation sets
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem puncture_etale_iff (R : CommRingCat.{u})
    (A : Type u) [CommRing A] [Algebra R A] (r : R) :
    Etale (Scheme.Opens.ι (X := Spec (.of A))
      (PrimeSpectrum.basicOpen (algebraMap R A r)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
      Algebra.Etale R (Localization.Away (algebraMap R A r)) := by
  let S := Localization.Away (algebraMap R A r)
  let e := basicOpenIsoSpecAway (R := CommRingCat.of A) (algebraMap R A r)
  have hc : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Scheme.Opens.ι (X := Spec (.of A))
        (PrimeSpectrum.basicOpen (algebraMap R A r)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    dsimp [e, S]
    rw [IsScalarTower.algebraMap_eq R A (Localization.Away (algebraMap R A r))]
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [← hc]
  constructor
  · intro h
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
      have : Etale (e.inv ≫ (e.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R S)))) := inferInstance
      simpa using this
    exact RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)).mp this)
  · intro h
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr h)
    infer_instance

set_option linter.unusedVariables false in
/-- A subgroup quotient of a finite etale torsor is etale on the fixed principal open. -/
theorem affine_torsor_invariant_puncture_etale
    (H : CommRingCat.{u}) (h : H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C h ≠ 0)
    (hEt : Etale (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C))))
    (hrot : ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C h) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b)
    (K : Subgroup G) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    Etale (Scheme.Opens.ι (X := Spec (CommRingCat.of F))
      (PrimeSpectrum.basicOpen (algebraMap H F h)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H F))) := by
  intro F
  let T := Localization.Away h
  let σ : K → C →ₐ[H] C := fun ζ ↦ ρ ζ.val
  have hF : F = AlgHom.fixedPoints σ := by
    ext c
    simp only [F, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply,
      AlgHom.mem_fixedPoints, σ]
  let := Algebra.TensorProduct.rightAlgebra (R := H) (A := T) (B := C)
  let := Algebra.TensorProduct.rightAlgebra (R := H) (A := T) (B := F)
  let := Algebra.TensorProduct.rightAlgebra (R := H) (A := T)
    (B := AlgHom.fixedPoints σ)
  have : Algebra.Etale H (Localization.Away (algebraMap H C h)) :=
    (puncture_etale_iff H C h).mp hEt
  let eC := IsLocalization.Away.tensorRightEquiv (R := H) (A := T) (r := h) C
  have : Algebra.Etale H (TensorProduct H T C) :=
    Algebra.Etale.of_equiv (eC.restrictScalars H).symm
  have : Algebra.Etale H T := Algebra.Etale.of_isLocalizationAway h
  have : Algebra.Etale T (TensorProduct H T C) := Algebra.Etale.of_restrictScalars H T _
  have hfix := (AlgHom.finite_and_etale_fixedPoints (AlgHom.baseChangeFamily T σ)).2
  let efix := AlgHom.tensorFixedPointsEquiv T σ
  have : Algebra.Etale T (TensorProduct H T (AlgHom.fixedPoints σ)) :=
    Algebra.Etale.of_equiv efix.symm
  have : Algebra.Etale H (TensorProduct H T (AlgHom.fixedPoints σ)) :=
    Algebra.Etale.comp H T _
  let eF := Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T)
    (Subalgebra.equivOfEq F (AlgHom.fixedPoints σ) hF)
  have : Algebra.Etale H (TensorProduct H T F) :=
    Algebra.Etale.of_equiv (eF.restrictScalars H).symm
  let eAway := IsLocalization.Away.tensorRightEquiv (R := H) (A := T) (r := h) F
  have : Algebra.Etale H (Localization.Away (algebraMap H F h)) :=
    Algebra.Etale.of_equiv (eAway.restrictScalars H)
  exact (puncture_etale_iff H F h).mpr this

end AlgebraicGeometry.Scheme
