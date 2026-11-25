/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # GenericProductIdempotentBound

Generic finite-algebra calculation from the smooth purity blueprint.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

private theorem clear_span_denominator
    (D F M : Type*) [CommRing D] [IsDomain D] [Field F]
    [Algebra D F] [IsFractionRing D F] [AddCommGroup M]
    [Module F M] [Module D M] [IsScalarTower D F M]
    (S : Set M) (z : M) (hz : z ∈ Submodule.span F S) :
    ∃ d : D, d ≠ 0 ∧ d • z ∈ Submodule.span D S := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span hz⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨dx, hdx, hx⟩ := ihx
    obtain ⟨dy, hdy, hy⟩ := ihy
    refine ⟨dx * dy, mul_ne_zero hdx hdy, ?_⟩
    rw [smul_add]
    have h₁ := (Submodule.span D S).smul_mem dy hx
    have h₂ := (Submodule.span D S).smul_mem dx hy
    rw [smul_smul, mul_comm dy dx] at h₁
    rw [smul_smul] at h₂
    exact (Submodule.span D S).add_mem h₁ h₂
  | smul a x hx ih =>
    obtain ⟨d, hd, hx⟩ := ih
    obtain ⟨n, q, hq, ha⟩ := IsFractionRing.div_surjective D a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqF : algebraMap D F q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    refine ⟨q * d, mul_ne_zero hq0 hd, ?_⟩
    have hqa : algebraMap D F q * a = algebraMap D F n := by
      rw [← ha, mul_div_cancel₀ _ hqF]
    have heq : (q * d) • (a • x) = n • (d • x) := by
      simp only [← IsScalarTower.algebraMap_smul F (q * d),
        ← IsScalarTower.algebraMap_smul F n, ← IsScalarTower.algebraMap_smul F d,
        map_mul, smul_smul]
      congr 1
      rw [mul_right_comm, hqa]
    rw [heq]
    exact (Submodule.span D S).smul_mem n hx

/-- After one principal localization, every reduced generic product map compatible
with the fixed splitting contains all the coordinate idempotents in its image.

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-generic-product-idempotent-bound)

Proof: Put C = (B tensor_A R0)_red. Tensor associativity and localization
of the nilradical identify its generic localization with the given product via e.
For each of the finitely many coordinate idempotents, choose a numerator in C and a
nonzero R0 denominator. Take t to be the product of these denominators. It is nonzero
because R0 is a domain. If t divides s, every denominator divides s, hence is a unit
in R0[1/s]. Map the chosen numerator to (B tensor_A R)_red and multiply it by the
inverse of the image of its denominator. Its image in the generic product is exactly
the desired coordinate idempotent. Compatibility on pure tensors, together with
R-linearity and surjectivity of the quotient, identifies any specified f with this
canonical map, so the construction works for every such f. For r = 0 choose t = 1;
there is no coordinate to lift. Neither injectivity nor Noetherianity is used. -/
theorem exists_generic_product_idempotent_bound
    (A : Type u) [CommRing A]
    (B : Type v) [CommRing B] [Algebra A B]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (K' : Type (max u v)) [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K']
    (R0 : Type (max u v)) [CommRing R0] [IsDomain R0]
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
          (∀ j, ∃ x, ∀ i, f x i = if i = j then 1 else 0) := by
  classical
  let := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
  let (j : Fin r) : Algebra R0 (L j) :=
    ((algebraMap K' (L j)).comp (algebraMap R0 K')).toAlgebra
  let (j : Fin r) : IsScalarTower R0 K' (L j) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let q := e.toAlgHom.comp (Ideal.Quotient.mkₐ K' _)
  let g : B → (∀ j, L j) := fun b ↦ q (((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (1 : K'))
  have hspan (z : ∀ j, L j) : z ∈ Submodule.span K' (Set.range g) := by
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (e.symm z)
    have hqw : q w = z := by simp [q, Ideal.Quotient.mkₐ_eq_mk, hw]
    rw [← hqw]
    clear hw hqw
    induction w using TensorProduct.inductionOn with
    | add x y hx hy => simpa using (Submodule.span K' (Set.range g)).add_mem hx hy
    | tmul x c =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
        simpa only [TensorProduct.add_tmul, map_add] using
          (Submodule.span K' (Set.range g)).add_mem hx hy
      | tmul k b =>
        have ht : ((k ⊗ₜ[A] b) ⊗ₜ[K] c) =
            (c * algebraMap K K' k) • (((1 : K) ⊗ₜ[A] b) ⊗ₜ[K] (1 : K')) := by
          rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
          rw [show (k ⊗ₜ[A] b) = k • ((1 : K) ⊗ₜ[A] b) by
            simp [TensorProduct.smul_tmul']]
          rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
        rw [ht, map_smul]
        exact (Submodule.span K' (Set.range g)).smul_mem _
          (Submodule.subset_span ⟨b, rfl⟩)
  let z : Fin r → (∀ i, L i) := fun j i ↦ if i = j then 1 else 0
  have hd (j : Fin r) := clear_span_denominator R0 K' (∀ i, L i)
    (Set.range g) (z j) (hspan (z j))
  choose d hd0 hdspan using hd
  refine ⟨∏ j, d j, Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hd0 j), ?_⟩
  intro s hs R _ _ _ _ _ _ _ _ _ _
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := R)
  intro f hf j
  have hdunit : IsUnit (algebraMap R0 R (d j)) :=
    IsLocalization.Away.isUnit_of_dvd s
      ((Finset.dvd_prod_of_mem d (Finset.mem_univ j)).trans hs)
  let (i : Fin r) : IsScalarTower R0 R (L i) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap K' (L i) (algebraMap R0 K' a) = _
      rw [IsScalarTower.algebraMap_apply R0 R K',
        IsScalarTower.algebraMap_apply R K' (L i)]
  let C := (B ⊗[A] R) ⧸ nilradical (B ⊗[A] R)
  let : Algebra R0 C := ((algebraMap R C).comp (algebraMap R0 R)).toAlgebra
  let : IsScalarTower R0 R C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let F := f.toLinearMap.restrictScalars R0
  have hle : Submodule.span R0 (Set.range g) ≤ F.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk _ (b ⊗ₜ[A] (1 : R)), hf b⟩
  obtain ⟨x, hx⟩ := hle (hdspan j)
  obtain ⟨u, hu⟩ := hdunit
  refine ⟨(↑u⁻¹ : R) • x, ?_⟩
  have hfx : f x = (algebraMap R0 R (d j)) • z j := by
    change f x = d j • z j at hx
    simpa only [← IsScalarTower.algebraMap_smul R (d j)] using hx
  have heq : f ((↑u⁻¹ : R) • x) = z j := by
    rw [map_smul, hfx, ← hu, smul_smul]
    simp
  intro i
  exact congrFun heq i
