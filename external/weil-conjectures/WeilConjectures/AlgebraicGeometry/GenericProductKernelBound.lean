/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas

import WeilConjectures.AlgebraicGeometry.GenericTensorNilpotenceAnnihilator
import WeilConjectures.AlgebraicGeometry.GenericTensorNilpotenceDescent


/-! # GenericProductKernelBound

Generic finite-algebra calculation from the smooth purity blueprint.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

/-- After one principal localization, every reduced generic product map compatible
with the fixed generic splitting is injective, including after further localization.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-generic-product-kernel-bound)

Proof: Put C = (B tensor_A R0)_red. It is a finite R0-module. Tensor
associativity identifies its generic localization with the source of e: reduction
commutes with localization, since a fraction is nilpotent if and only if a denominator
multiple of its numerator is nilpotent. The kernel of the map from C to its generic
localization is torsion and finitely generated, since R0 is Noetherian. Choose a
nonzero annihilator for each generator and take their product t (1 for no generators).
Localizing at any s divisible by t kills the kernel. Localization is exact, so the
induced map from the localized C to the generic product is injective. Reduction
commutes with this principal localization and identifies its source with
(B tensor_A R)_red. The pure-tensor compatibility determines the map f uniquely:
R-linearity determines all pure tensors and additivity determines their sums; the
quotient map is surjective. Thus f is the injective induced map. When the generic
product is zero, the kernel is all of C and the same torsion argument kills C. -/
theorem exists_generic_product_kernel_bound
    (A : Type u) [CommRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (K' : Type (max u v)) [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K']
    (R0 : Type (max u v)) [CommRing R0] [IsNoetherianRing R0]
    [IsDomain R0]
    [Algebra A R0] [Algebra R0 K'] [IsScalarTower A R0 K']
    [IsFractionRing R0 K']
    (r : ℕ) (L : Fin r → Type (max u v)) [∀ j, Field (L j)]
    [∀ j, Algebra K' (L j)]
    (e :
      letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
      (((K ⊗[A] B) ⊗[K] K') ⧸
        nilradical ((K ⊗[A] B) ⊗[K] K')) ≃ₐ[K'] (∀ j, L j))
    : ∃ t : R0, t ≠ 0 ∧ ∀ s : R0, t ∣ s →
      ∀ (R : Type u) [CommRing R] [Algebra R0 R] [IsLocalization.Away s R]
        [Algebra A R] [IsScalarTower A R0 R] [Algebra R K']
        [IsScalarTower R0 R K'] [IsFractionRing R K']
        [∀ j, Algebra R (L j)] [∀ j, IsScalarTower R K' (L j)],
        letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)
        ∀ f : ((B ⊗[A] R) ⧸ nilradical (B ⊗[A] R)) →ₐ[R] (∀ j, L j),
            (∀ b : B, f (Ideal.Quotient.mk _ (b ⊗ₜ[A] (1 : R))) =
              e (Ideal.Quotient.mk _ (((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (1 : K')))) →
          Function.Injective f := by
  obtain ⟨t, ht, hnil⟩ := exists_generic_tensor_nilpotence_annihilator A B R0 K'
  refine ⟨t, ht, ?_⟩
  intro s hts R _ _ _ _ _ _ _ _ _ _ f hf
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)
  let := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
  let : IsScalarTower A R K' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A R0 K',
      IsScalarTower.algebraMap_apply A R0 R,
      IsScalarTower.algebraMap_apply R0 R K']
  let ψ : (B ⊗[A] K') ≃+* ((K ⊗[A] B) ⊗[K] K') :=
    (Algebra.TensorProduct.comm A B K').toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange A K K' K' B).symm.toRingEquiv.trans
        (Algebra.TensorProduct.comm K K' (K ⊗[A] B)).toRingEquiv)
  let m := Algebra.TensorProduct.map (AlgHom.id A B) (IsScalarTower.toAlgHom A R K')
  have hψ (b : B) (c : K') : ψ (b ⊗ₜ[A] c) = ((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] c := by
    simp [ψ]
  have hcompat (x : B ⊗[A] R) :
      f (Ideal.Quotient.mk _ x) = e (Ideal.Quotient.mk _ (ψ (m x))) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul b c =>
      have hc : f (Ideal.Quotient.mk _ ((1 : B) ⊗ₜ[A] c)) =
          algebraMap R (∀ j, L j) c := f.commutes c
      have hc' : e (Ideal.Quotient.mk _
          ((1 : K ⊗[A] B) ⊗ₜ[K] (algebraMap R K' c))) =
          algebraMap R (∀ j, L j) c := by
        rw [show Ideal.Quotient.mk _
            ((1 : K ⊗[A] B) ⊗ₜ[K] (algebraMap R K' c)) =
            algebraMap K' _ (algebraMap R K' c) from rfl,
          e.commutes, ← IsScalarTower.algebraMap_apply R K' (∀ j, L j)]
      have hs : b ⊗ₜ[A] c = (b ⊗ₜ[A] (1 : R)) * ((1 : B) ⊗ₜ[A] c) := by
        simp
      have hg : ((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (algebraMap R K' c) =
          (((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (1 : K')) *
            ((1 : K ⊗[A] B) ⊗ₜ[K] (algebraMap R K' c)) := by simp
      simp only [m, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        hψ]
      change f (Ideal.Quotient.mk _ (b ⊗ₜ[A] c)) =
        e (Ideal.Quotient.mk _ (((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (algebraMap R K' c)))
      rw [hs, hg, map_mul, map_mul, map_mul, map_mul, hf b, hc, hc']
  apply (injective_iff_map_eq_zero f).2
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : IsNilpotent (m y) := by
    have hz : Ideal.Quotient.mk (nilradical ((K ⊗[A] B) ⊗[K] K')) (ψ (m y)) = 0 :=
      e.injective (by simpa only [map_zero] using (hcompat y).symm.trans hx)
    have hn := mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    exact (IsNilpotent.map_iff ψ.injective).mp hn
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact mem_nilradical.mpr
    (generic_tensor_nilpotence_of_annihilator A B R0 K' t hnil s hts R y hy)
