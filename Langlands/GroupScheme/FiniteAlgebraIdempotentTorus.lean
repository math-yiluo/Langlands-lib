import Langlands.GroupScheme.FiniteAlgebraUnits
import Langlands.GroupScheme.Multiplicative
import Mathlib.Tactic.Module

/-! # A multiplicative-group map from two orthogonal idempotents -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteAlgebraUnits

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  (p q : A) (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0)

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The unit candidate scaling the two idempotent summands inversely. -/
def idempotentScalingValue (t : Rˣ) : R ⊗[K] A :=
  1 + ((t : R) - 1) • ((1 : R) ⊗ₜ[K] p) +
    (((t⁻¹ : Rˣ) : R) - 1) • ((1 : R) ⊗ₜ[K] q)

theorem idempotentScalingValue_eq (t : Rˣ) :
    idempotentScalingValue (K := K) p q R t =
      1 + ((t : R) - 1) ⊗ₜ[K] p + (((t⁻¹ : Rˣ) : R) - 1) ⊗ₜ[K] q := by
  simp [idempotentScalingValue, TensorProduct.smul_tmul']

@[simp] theorem idempotentScalingValue_one : idempotentScalingValue (K := K) p q R 1 = 1 := by
  simp [idempotentScalingValue]

include hp hq hpq hqp in
/-- Orthogonal idempotents give the multiplicative law on every coefficient algebra. -/
theorem idempotentScalingValue_mul (t s : Rˣ) :
    idempotentScalingValue (K := K) p q R (t * s) =
      idempotentScalingValue (K := K) p q R t * idempotentScalingValue (K := K) p q R s := by
  let P : R ⊗[K] A := 1 ⊗ₜ[K] p
  let Q : R ⊗[K] A := 1 ⊗ₜ[K] q
  have hP : P * P = P := by simp [P, Algebra.TensorProduct.tmul_mul_tmul, hp]
  have hQ : Q * Q = Q := by simp [Q, Algebra.TensorProduct.tmul_mul_tmul, hq]
  have hPQ : P * Q = 0 := by simp [P, Q, Algebra.TensorProduct.tmul_mul_tmul, hpq]
  have hQP : Q * P = 0 := by simp [P, Q, Algebra.TensorProduct.tmul_mul_tmul, hqp]
  change 1 + ((↑(t * s) : R) - 1) • P + ((↑((t * s)⁻¹) : R) - 1) • Q =
    (1 + ((t : R) - 1) • P + ((↑t⁻¹ : R) - 1) • Q) *
      (1 + ((s : R) - 1) • P + ((↑s⁻¹ : R) - 1) • Q)
  simp only [Units.val_mul, mul_inv_rev, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hP, hQ, hPQ, hQP,
    smul_zero, add_zero]
  module

/-- The coefficient-algebra unit homomorphism supplied by an orthogonal idempotent pair. -/
def idempotentScalingUnits : Rˣ →* (R ⊗[K] A)ˣ where
  toFun t :=
    { val := idempotentScalingValue (K := K) p q R t
      inv := idempotentScalingValue (K := K) p q R t⁻¹
      val_inv := by rw [← idempotentScalingValue_mul p q hp hq hpq hqp,
        mul_inv_cancel, idempotentScalingValue_one]
      inv_val := by rw [← idempotentScalingValue_mul p q hp hq hpq hqp,
        inv_mul_cancel, idempotentScalingValue_one] }
  map_one' := Units.ext (idempotentScalingValue_one p q R)
  map_mul' t s := Units.ext (idempotentScalingValue_mul p q hp hq hpq hqp R t s)

variable {R} {S : Type u} [CommRing S] [Algebra K S]

/-- This unit construction commutes with every coefficient-algebra homomorphism. -/
theorem idempotentScalingUnits_map (φ : R →ₐ[K] S) (t : Rˣ) :
    Units.map (Algebra.TensorProduct.map φ (AlgHom.id K A)).toMonoidHom
        (idempotentScalingUnits (K := K) p q hp hq hpq hqp R t) =
      idempotentScalingUnits (K := K) p q hp hq hpq hqp S (Units.map φ.toMonoidHom t) := by
  apply Units.ext
  change Algebra.TensorProduct.map φ (AlgHom.id K A) (idempotentScalingValue (K := K) p q R t) =
    idempotentScalingValue (K := K) p q S (Units.map φ.toMonoidHom t)
  simp [idempotentScalingValue_eq]

variable {d : ℕ} (b : Module.Basis (Fin d) K A)

/-- The natural homomorphism on actual scheme points. -/
def idempotentScalingPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (Gm (Spec (CommRingCat.of K))).X) →* (T ⟶ (groupScheme b).X) :=
  (pointsEquiv b T).symm.toMonoidHom.comp
    ((idempotentScalingUnits (K := K) p q hp hq hpq hqp
      (((algΓ (CommRingCat.of K)).obj T).unop)).comp
        (Gm.pointsEquiv (Spec (CommRingCat.of K)) T).toMonoidHom)

theorem idempotentScalingPoints_equiv {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of K))).X) :
    pointsEquiv b T (idempotentScalingPoints p q hp hq hpq hqp b T x) =
      idempotentScalingUnits (K := K) p q hp hq hpq hqp
        (((algΓ (CommRingCat.of K)).obj T).unop)
        (Gm.pointsEquiv (Spec (CommRingCat.of K)) T x) :=
  (pointsEquiv b T).apply_symm_apply _

/-- Naturality on all tests realizes the actual multiplicative-group morphism. -/
theorem idempotentScalingPoints_naturality
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (Gm (Spec (CommRingCat.of K))).X) :
    idempotentScalingPoints p q hp hq hpq hqp b T' (a ≫ x) =
      a ≫ idempotentScalingPoints p q hp hq hpq hqp b T x := by
  apply (pointsEquiv b T').injective
  rw [pointsEquiv_naturality, idempotentScalingPoints_equiv,
    idempotentScalingPoints_equiv, Gm.pointsEquiv_naturality]
  exact (idempotentScalingUnits_map p q hp hq hpq hqp
    (((algΓ (CommRingCat.of K)).map a).unop.hom) _).symm

/-- The actual torus morphism scaling two orthogonal idempotent summands inversely. -/
def idempotentScalingHom :
    (Gm (Spec (CommRingCat.of K))).toGrp ⟶ groupScheme b :=
  homOfPoints (idempotentScalingPoints p q hp hq hpq hqp b)
    (idempotentScalingPoints_naturality p q hp hq hpq hqp b)

theorem idempotentScalingHom_points {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of K))).X) :
    pointsEquiv b T (x ≫ (idempotentScalingHom p q hp hq hpq hqp b).hom.hom) =
      idempotentScalingUnits (K := K) p q hp hq hpq hqp
        (((algΓ (CommRingCat.of K)).obj T).unop)
        (Gm.pointsEquiv (Spec (CommRingCat.of K)) T x) := by
  rw [idempotentScalingHom, comp_homOfPoints]
  exact (pointsEquiv b T).apply_symm_apply _

end Langlands.GroupScheme.FiniteAlgebraUnits
