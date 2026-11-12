import Langlands.GroupScheme.FiniteAlgebraIdempotentTorus
import Langlands.GroupScheme.Dynamic.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Contracting elements for an idempotent torus

Let `p, q` be orthogonal idempotents of a finite-dimensional `K`-algebra `A` and let
`μ = idempotentScalingHom p q` be the cocharacter `t ↦ 1 + (t - 1) p + (t⁻¹ - 1) q` of the unit
group scheme of `A`. If `N₁` has weight `1` and `N₂` has weight `2` for the conjugation action
of `μ` (`IsContracting p q N₁ N₂`), then `μ(t) (1 + N₁ + N₂) μ(t)⁻¹ = 1 + t N₁ + t² N₂`, and the
point `1 + N₁ + N₂` lies in the dynamic unipotent subgroup `U(μ)` on every test scheme.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits

section Algebra

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]

/-- `N₁` has weight `1` and `N₂` has weight `2` for the conjugation action of the idempotent
torus of `(p, q)`: `N₁ p = 0`, `q N₁ = 0`, `p N₁ q = 0`, `p N₁ + N₁ q = N₁`, and `N₂ p = 0`,
`q N₂ = 0`, `N₂ q = N₂`, `p N₂ = N₂`. -/
structure IsContracting (p q N₁ N₂ : A) : Prop where
  one_mul_left : N₁ * p = 0
  right_mul_one : q * N₁ = 0
  left_one_right : p * N₁ * q = 0
  decomp : p * N₁ + N₁ * q = N₁
  two_mul_left : N₂ * p = 0
  right_mul_two : q * N₂ = 0
  two_mul_right : N₂ * q = N₂
  left_mul_two : p * N₂ = N₂

namespace IsContracting

variable {p q N₁ N₂ : A} (h : IsContracting p q N₁ N₂)
include h

theorem one_mul_two : N₁ * N₂ = 0 := by
  rw [← h.left_mul_two, ← mul_assoc, h.one_mul_left, zero_mul]

theorem two_mul_one : N₂ * N₁ = 0 := by
  rw [← h.two_mul_right, mul_assoc, h.right_mul_one, mul_zero]

theorem two_mul_two : N₂ * N₂ = 0 := by
  calc N₂ * N₂ = N₂ * q * N₂ := by rw [h.two_mul_right]
    _ = 0 := by rw [mul_assoc, h.right_mul_two, mul_zero]

theorem one_mul_one_mul_one : N₁ * (N₁ * N₁) = 0 := by
  have h11 : N₁ * N₁ = p * (N₁ * N₁) := by
    calc N₁ * N₁ = (p * N₁ + N₁ * q) * N₁ := by rw [h.decomp]
      _ = p * (N₁ * N₁) := by
        rw [add_mul, mul_assoc, mul_assoc N₁ q N₁, h.right_mul_one, mul_zero, add_zero]
  rw [h11, ← mul_assoc, h.one_mul_left, zero_mul]

end IsContracting

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The value `1 + s N₁ + s² N₂` over a coefficient algebra `R`. -/
def contractingValue (N₁ N₂ : A) (s : R) : R ⊗[K] A :=
  1 + s ⊗ₜ[K] N₁ + (s ^ 2) ⊗ₜ[K] N₂

/-- Its inverse `1 - s N₁ + (s N₁)² - s² N₂`. -/
def contractingInvValue (N₁ N₂ : A) (s : R) : R ⊗[K] A :=
  1 - s ⊗ₜ[K] N₁ + (s ⊗ₜ[K] N₁) * (s ⊗ₜ[K] N₁) - (s ^ 2) ⊗ₜ[K] N₂

variable {R}

section Relations

variable {p q N₁ N₂ : A} (h : IsContracting p q N₁ N₂) (s : R)
include h

theorem tmul_mul_tmul_two : (s ⊗ₜ[K] N₁) * ((s ^ 2) ⊗ₜ[K] N₂) = 0 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, h.one_mul_two, TensorProduct.tmul_zero]

theorem tmul_two_mul_tmul : ((s ^ 2) ⊗ₜ[K] N₂) * (s ⊗ₜ[K] N₁) = 0 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, h.two_mul_one, TensorProduct.tmul_zero]

theorem tmul_two_mul_tmul_two : ((s ^ 2) ⊗ₜ[K] N₂) * ((s ^ 2) ⊗ₜ[K] N₂) = 0 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, h.two_mul_two, TensorProduct.tmul_zero]

theorem tmul_cube : (s ⊗ₜ[K] N₁) * ((s ⊗ₜ[K] N₁) * (s ⊗ₜ[K] N₁)) = 0 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    h.one_mul_one_mul_one, TensorProduct.tmul_zero]

theorem contractingValue_mul_inv :
    contractingValue (K := K) R N₁ N₂ s * contractingInvValue (K := K) R N₁ N₂ s = 1 := by
  set X := s ⊗ₜ[K] N₁
  set Y := (s ^ 2) ⊗ₜ[K] N₂
  have e : (1 + X + Y) * (1 - X + X * X - Y) =
      1 + X * (X * X) - X * Y - Y * X + Y * X * X - Y * Y := by noncomm_ring
  simp only [contractingValue, contractingInvValue]
  rw [e, tmul_cube h s, tmul_mul_tmul_two h s, tmul_two_mul_tmul h s, tmul_two_mul_tmul_two h s]
  simp

theorem contractingInv_mul_value :
    contractingInvValue (K := K) R N₁ N₂ s * contractingValue (K := K) R N₁ N₂ s = 1 := by
  set X := s ⊗ₜ[K] N₁
  set Y := (s ^ 2) ⊗ₜ[K] N₂
  have e : (1 - X + X * X - Y) * (1 + X + Y) =
      1 - X * Y + X * (X * X) + X * (X * Y) - Y * X - Y * Y := by noncomm_ring
  simp only [contractingValue, contractingInvValue]
  rw [e, tmul_cube h s, tmul_mul_tmul_two h s, tmul_two_mul_tmul h s, tmul_two_mul_tmul_two h s]
  simp

end Relations

/-- The unit `1 + s N₁ + s² N₂`. -/
def contractingUnit {p q N₁ N₂ : A} (h : IsContracting p q N₁ N₂) (s : R) : (R ⊗[K] A)ˣ where
  val := contractingValue (K := K) R N₁ N₂ s
  inv := contractingInvValue (K := K) R N₁ N₂ s
  val_inv := contractingValue_mul_inv h s
  inv_val := contractingInv_mul_value h s

section Conjugation

variable {p q N₁ N₂ : A} (h : IsContracting p q N₁ N₂)

@[simp] theorem val_contractingUnit (s : R) :
    (contractingUnit (K := K) h s : R ⊗[K] A) = contractingValue (K := K) R N₁ N₂ s :=
  rfl

theorem contractingUnit_zero : contractingUnit (K := K) h (0 : R) = 1 := by
  apply Units.ext
  simp [contractingValue]

variable {S : Type u} [CommRing S] [Algebra K S]

theorem contractingUnit_map (φ : R →ₐ[K] S) (s : R) :
    Units.map (Algebra.TensorProduct.map φ (AlgHom.id K A)).toMonoidHom (contractingUnit h s) =
      contractingUnit h (φ s) := by
  apply Units.ext
  change Algebra.TensorProduct.map φ (AlgHom.id K A) (contractingValue (K := K) R N₁ N₂ s) =
    contractingValue (K := K) S N₁ N₂ (φ s)
  simp [contractingValue]

variable (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0)
include hp hq hpq hqp

/-- **Contraction.** Conjugating `1 + N₁ + N₂` by the idempotent scaling `μ(t)` gives
`1 + t N₁ + t² N₂`. -/
theorem idempotentScalingUnits_conj (t : Rˣ) :
    idempotentScalingUnits (K := K) p q hp hq hpq hqp R t * contractingUnit h (1 : R) *
        (idempotentScalingUnits (K := K) p q hp hq hpq hqp R t)⁻¹ =
      contractingUnit h (t : R) := by
  apply Units.ext
  change idempotentScalingValue (K := K) p q R t * contractingValue (K := K) R N₁ N₂ 1 *
      idempotentScalingValue (K := K) p q R t⁻¹ = contractingValue (K := K) R N₁ N₂ t
  have hVV := idempotentScalingValue_mul (K := K) p q hp hq hpq hqp R t t⁻¹
  rw [mul_inv_cancel, idempotentScalingValue_one] at hVV
  have hv : ∀ (r : R) (N : A), r ⊗ₜ[K] N = r • ((1 : R) ⊗ₜ[K] N) := fun r N => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [idempotentScalingValue, contractingValue, inv_inv, one_pow] at hVV ⊢
  rw [hv (t : R) N₁, hv ((t : R) ^ 2) N₂]
  set P : R ⊗[K] A := 1 ⊗ₜ[K] p
  set Q : R ⊗[K] A := 1 ⊗ₜ[K] q
  set X : R ⊗[K] A := 1 ⊗ₜ[K] N₁
  set Y : R ⊗[K] A := 1 ⊗ₜ[K] N₂
  set a : R := (t : R) - 1
  set b : R := ((t⁻¹ : Rˣ) : R) - 1
  have tm : ∀ c d : A, ((1 : R) ⊗ₜ[K] c) * ((1 : R) ⊗ₜ[K] d) = (1 : R) ⊗ₜ[K] (c * d) := by
    intro c d
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hXP : X * P = 0 := by rw [tm, h.one_mul_left, TensorProduct.tmul_zero]
  have hQX : Q * X = 0 := by rw [tm, h.right_mul_one, TensorProduct.tmul_zero]
  have hPXQ : P * (X * Q) = 0 := by
    rw [tm, tm, ← mul_assoc, h.left_one_right, TensorProduct.tmul_zero]
  have hYP : Y * P = 0 := by rw [tm, h.two_mul_left, TensorProduct.tmul_zero]
  have hQY : Q * Y = 0 := by rw [tm, h.right_mul_two, TensorProduct.tmul_zero]
  have hYQ : Y * Q = Y := by rw [tm, h.two_mul_right]
  have hPY : P * Y = Y := by rw [tm, h.left_mul_two]
  have hdec : P * X = X - X * Q := by
    rw [eq_sub_iff_add_eq, tm, tm, ← TensorProduct.tmul_add, h.decomp]
  set V : R ⊗[K] A := 1 + a • P + b • Q
  set V' : R ⊗[K] A := 1 + b • P + a • Q
  have h2 : V * X * V' = (t : R) • X := by
    simp only [V, V', add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      mul_assoc, hQX, hXP, hPXQ, smul_zero, add_zero]
    rw [hdec]
    simp only [a, mul_zero, smul_zero, add_zero]
    module
  have h3 : V * Y * V' = ((t : R) ^ 2) • Y := by
    simp only [V, V', add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      hQY, hYP, hYQ, hPY, smul_zero, add_zero]
    simp only [a]
    module
  have e : V * (1 + X + Y) * V' = V * V' + V * X * V' + V * Y * V' := by noncomm_ring
  rw [e, ← hVV, h2, h3]
end Conjugation

end Algebra

section Scheme

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  {p q N₁ N₂ : A} (h : IsContracting p q N₁ N₂)
  (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0)
  {d : ℕ} (b : Module.Basis (Fin d) K A)

/-- The point `1 + N₁ + N₂` of the unit group scheme on a test scheme `T`. -/
def contractingPoint (T : Over (Spec (CommRingCat.of K))) : T ⟶ (groupScheme b).X :=
  (pointsEquiv b T).symm
    (contractingUnit (K := K) (R := ((algΓ (CommRingCat.of K)).obj T).unop) h 1)

/-- The curve `s ↦ 1 + s N₁ + s² N₂` on `T × 𝔸¹`. -/
def contractingCurve (T : Over (Spec (CommRingCat.of K))) :
    T ⊗ AffineLine.scheme (Spec (CommRingCat.of K)) ⟶ (groupScheme b).X :=
  (pointsEquiv b _).symm
    (contractingUnit (K := K)
      (R := ((algΓ (CommRingCat.of K)).obj
        (T ⊗ AffineLine.scheme (Spec (CommRingCat.of K)))).unop) h
      (AffineLine.homEquiv _ (snd T (AffineLine.scheme (Spec (CommRingCat.of K))))))

/-- The contracting point is compatible with every change of test scheme. -/
theorem comp_contractingPoint {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T) :
    a ≫ contractingPoint h b T = contractingPoint h b T' := by
  apply (pointsEquiv b T').injective
  rw [pointsEquiv_naturality, contractingPoint, contractingPoint, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]
  exact (contractingUnit_map h _ 1).trans (by rw [map_one])

include hp hq hpq hqp in
/-- **Contracting points.** The point `1 + N₁ + N₂` lies in the dynamic unipotent subgroup of
the idempotent torus `idempotentScalingHom p q`. -/
theorem contractingPoint_mem_unipotent (T : Over (Spec (CommRingCat.of K))) :
    contractingPoint h b T ∈
      (Dynamic.unipotent (idempotentScalingHom p q hp hq hpq hqp b)).carrier T := by
  refine ⟨contractingCurve h b T, ?_, ?_⟩
  · apply (pointsEquiv b _).injective
    have hL : pointsEquiv b _
        (T ◁ AffineLine.unitInclusion (Spec (CommRingCat.of K)) ≫ contractingCurve h b T) =
        contractingUnit (K := K)
          (R := ((algΓ (CommRingCat.of K)).obj (T ⊗ (Gm (Spec (CommRingCat.of K))).X)).unop) h
          (Gm.pointsEquiv (Spec (CommRingCat.of K)) _
            (snd T (Gm (Spec (CommRingCat.of K))).X)).val := by
      rw [contractingCurve, pointsEquiv_naturality, MulEquiv.apply_symm_apply]
      erw [contractingUnit_map]
      congr 1
      change (T ◁ AffineLine.unitInclusion _).left.appTop
        (AffineLine.homEquiv _ (snd T (AffineLine.scheme (Spec (CommRingCat.of K))))) = _
      rw [← AffineLine.homEquiv_comp, whiskerLeft_snd, AffineLine.homEquiv_comp_unitInclusion]
    have hR : pointsEquiv b _
        (Dynamic.orbit (idempotentScalingHom p q hp hq hpq hqp b) (contractingPoint h b T)) =
        contractingUnit (K := K)
          (R := ((algΓ (CommRingCat.of K)).obj (T ⊗ (Gm (Spec (CommRingCat.of K))).X)).unop) h
          (Gm.pointsEquiv (Spec (CommRingCat.of K)) _
            (snd T (Gm (Spec (CommRingCat.of K))).X)).val := by
      rw [Dynamic.orbit, comp_contractingPoint, map_mul, map_mul, map_inv,
        idempotentScalingHom_points, contractingPoint, MulEquiv.apply_symm_apply]
      exact idempotentScalingUnits_conj h hp hq hpq hqp _
    exact hL.trans hR.symm
  · apply (pointsEquiv b T).injective
    have hE : pointsEquiv b T (Dynamic.evalZero (contractingCurve h b T)) =
        contractingUnit (K := K) (R := ((algΓ (CommRingCat.of K)).obj T).unop) h 0 := by
      rw [Dynamic.evalZero, contractingCurve, pointsEquiv_naturality, MulEquiv.apply_symm_apply]
      refine (contractingUnit_map h _ _).trans (congrArg (contractingUnit (K := K) h) ?_)
      change (lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection _)).left.appTop
        (AffineLine.homEquiv _ (snd T (AffineLine.scheme (Spec (CommRingCat.of K))))) = 0
      rw [← AffineLine.homEquiv_comp, lift_snd, AffineLine.homEquiv_comp_zeroSection]
    rw [hE, contractingUnit_zero, map_one]
end Scheme

end Langlands.GroupScheme.FiniteAlgebraUnits
