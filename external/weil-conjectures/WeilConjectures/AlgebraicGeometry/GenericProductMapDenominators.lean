/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # GenericProductMapDenominators

Generic finite-algebra calculation from the smooth purity blueprint.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

/-- A vector in the fraction-field span of an R-linear image has a nonzero
R-multiple in that image. Span induction multiplies denominators for sums and
uses a numerator and denominator for each fraction-field scalar. -/
private theorem clear_denominator_of_span
    {R F M V : Type*} [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    [AddCommGroup M] [Module R M] [AddCommGroup V] [Module F V] [Module R V]
    [IsScalarTower R F V] (h : M →ₗ[R] V) (y : V)
    (hy : y ∈ Submodule.span F (Set.range h)) :
    ∃ a : R, a ≠ 0 ∧ ∃ x : M, a • y = h x := by
  have : IsDomain R := Function.Injective.isDomain (algebraMap R F) (IsFractionRing.injective R F)
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact ⟨1, one_ne_zero, x, one_smul _ _⟩
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, x, hx⟩ := hy
    obtain ⟨b, hb, w, hw⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, b • x + a • w, ?_⟩
    rw [map_add, map_smul, map_smul, ← hx, ← hw, smul_add, mul_smul, mul_smul]
    rw [smul_comm b a y]
  | smul c y _ hy =>
    obtain ⟨a, ha, x, hx⟩ := hy
    obtain ⟨n, d, hd, hc⟩ := IsFractionRing.div_surjective R c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdc : algebraMap R F d * c = algebraMap R F n := by
      rw [← hc, mul_div_cancel₀ _
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)]
    refine ⟨d * a, mul_ne_zero hd0 ha, n • x, ?_⟩
    rw [map_smul, ← hx, mul_smul, smul_comm a c y, ← smul_assoc]
    rw [Algebra.smul_def d c, hdc, IsScalarTower.algebraMap_smul]

/-- A generic splitting defines the reduced base-change map, with coordinate denominator
clearing and a specified value on the image of every element of the original algebra.
Neither finiteness nor Noetherianity is needed for this assertion.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-generic-product-map-denominators)

Proof: Tensor associativity and commutation identify B tensor_A K' with
(K tensor_A B) tensor_K K'. The map B tensor_A R to this generic algebra followed
by the quotient and e kills every nilpotent, because a product of fields is reduced.
Thus it factors through the source reduction, giving f and the pure-tensor identity.
For z in L_j, apply e inverse to the vector supported at j with value z. Every element
of B tensor_A K' is a finite sum of pure tensors. Write their K' coefficients as
fractions over R, multiply the finitely many nonzero denominators, and lift the
resulting numerator to B tensor_A R. Passing to the quotient gives a*z = f(x)_j.
The product denominator is nonzero: R embeds in its fraction field K'. Empty sums
use denominator 1. If r is zero the coordinate assertion is vacuous. -/
theorem exists_generic_product_map_denominators
    (A : Type u) [CommRing A]
    (B : Type v) [CommRing B] [Algebra A B]
    (K : Type u) [Field K] [Algebra A K]
    (K' : Type (max u v)) [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K']
    (r : ℕ) (L : Fin r → Type (max u v)) [∀ j, Field (L j)]
    [∀ j, Algebra K' (L j)]
    (e :
      letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
      (((K ⊗[A] B) ⊗[K] K') ⧸
        nilradical ((K ⊗[A] B) ⊗[K] K')) ≃ₐ[K'] (∀ j, L j))
    (R : Type u) [CommRing R] [Algebra A R] [Algebra R K']
    [IsScalarTower A R K'] [IsFractionRing R K']
    [∀ j, Algebra R (L j)] [∀ j, IsScalarTower R K' (L j)] :
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)
    ∃ f : ((B ⊗[A] R) ⧸ nilradical (B ⊗[A] R)) →ₐ[R] (∀ j, L j),
            (∀ b : B, f (Ideal.Quotient.mk _ (b ⊗ₜ[A] (1 : R))) =
              e (Ideal.Quotient.mk _ (((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (1 : K')))) ∧
            (∀ j (z : L j), ∃ a : R, a ≠ 0 ∧
              ∃ x, algebraMap R (L j) a * z = f x j) := by
  let := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)
  let : Algebra A (∀ j, L j) := Algebra.restrictScalars A R (∀ j, L j)
  let : IsScalarTower A R (∀ j, L j) := .restrictScalars A R (∀ j, L j)
  let : IsScalarTower A K' (∀ j, L j) := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A R (∀ j, L j)]
    ext j
    change algebraMap R (L j) (algebraMap A R a) = _
    rw [IsScalarTower.algebraMap_apply R K' (L j)]
    rw [IsScalarTower.algebraMap_apply A R K']
    rfl
  let T := (K ⊗[A] B) ⊗[K] K'
  let : IsScalarTower A K' T := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change ((algebraMap A K a) ⊗ₜ[A] (1 : B)) ⊗ₜ[K] (1 : K') =
      (1 : K ⊗[A] B) ⊗ₜ[K] algebraMap A K' a
    rw [IsScalarTower.algebraMap_apply A K K']
    rw [Algebra.algebraMap_eq_smul_one (R := K) (A := K'), TensorProduct.tmul_smul]
    simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
      Algebra.algebraMap_eq_smul_one]
  let p : T →ₐ[K'] (∀ j, L j) :=
    e.toAlgHom.comp (Ideal.Quotient.mkₐ K' (nilradical T))
  let g : B →ₐ[A] (∀ j, L j) :=
    (p.restrictScalars A).comp
      ((Algebra.TensorProduct.includeLeft : K ⊗[A] B →ₐ[K] T).restrictScalars A |>.comp
        Algebra.TensorProduct.includeRight)
  let h : B ⊗[A] R →ₐ[R] (∀ j, L j) :=
    ((AlgHom.liftEquiv A R B (∀ j, L j)) g).comp
      (Algebra.TensorProduct.commRight A R B).symm.toAlgHom
  have hh (b : B) (a : R) : h (b ⊗ₜ[A] a) = a • g b := by
    simp [h]
  have hn (x : B ⊗[A] R) (hx : x ∈ nilradical (B ⊗[A] R)) : h x = 0 := by
    exact (show IsNilpotent (h x) from (mem_nilradical.mp hx).map h).eq_zero
  let f := Ideal.Quotient.liftₐ (nilradical (B ⊗[A] R)) h hn
  refine ⟨f, ?_, ?_⟩
  · intro b
    change h (b ⊗ₜ[A] (1 : R)) = _
    rw [hh, one_smul]
    rfl
  · intro j z
    let S := Submodule.span K' (Set.range h.toLinearMap)
    have hg (b : B) : g b ∈ S := by
      apply Submodule.subset_span
      exact ⟨b ⊗ₜ[A] (1 : R), by simpa using hh b 1⟩
    have hpure (k : K) (b : B) (t : K') :
        p ((k ⊗ₜ[A] b) ⊗ₜ[K] t) ∈ S := by
      have ht : (k ⊗ₜ[A] b) ⊗ₜ[K] t =
          (algebraMap K K' k * t) • ((1 ⊗ₜ[A] b) ⊗ₜ[K] (1 : K')) := by
        calc
          _ = (k • ((1 : K) ⊗ₜ[A] b)) ⊗ₜ[K] t := by
            simp [TensorProduct.smul_tmul']
          _ = ((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (k • t) :=
            TensorProduct.smul_tmul _ _ _
          _ = _ := by
            simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
              Algebra.TensorProduct.tmul_mul_tmul]
      rw [ht, map_smul]
      exact S.smul_mem _ (hg b)
    have hp (w : T) : p w ∈ S := by
      induction w using TensorProduct.inductionOn with
      | tmul q t =>
        induction q using TensorProduct.inductionOn with
        | tmul k b => exact hpure k b t
        | add q₁ q₂ h₁ h₂ =>
          simpa only [TensorProduct.add_tmul, map_add] using S.add_mem h₁ h₂
      | add w₁ w₂ h₁ h₂ => simpa only [map_add] using S.add_mem h₁ h₂
    classical
    let y : ∀ i, L i := Function.update 0 j z
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (e.symm y)
    have hy : y ∈ S := by
      have he : p w = y := by
        change e (Ideal.Quotient.mk _ w) = y
        rw [hw, e.apply_symm_apply]
      exact he ▸ hp w
    obtain ⟨a, ha, x, hx⟩ := clear_denominator_of_span h.toLinearMap y hy
    refine ⟨a, ha, Ideal.Quotient.mk _ x, ?_⟩
    have hxj := congrFun hx j
    change algebraMap R (L j) a * z = h x j
    simpa [y, Algebra.smul_def] using hxj

