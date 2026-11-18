import Langlands.GroupScheme.HomScheme.AdicInfinitesimalSteps
import Langlands.GroupScheme.InfinitesimalPowers
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Powers in nilpotent coefficient kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.NilpotentCoefficientPowers

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
  {A : Type u} [CommRing A] [Algebra R A]

/-- The transition between adjacent powers of an arbitrary ideal. -/
def transition (I : Ideal A) (n : ℕ) : A ⧸ I ^ (n + 2) →ₐ[R] A ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

theorem transition_ker_sq (I : Ideal A) (n : ℕ) :
    (RingHom.ker (transition (R := R) I n)) ^ 2 = ⊥ :=
  HomScheme.Adic.transitionRingHom_ker_sq I n

theorem transition_ker_annihilated (I : Ideal A) (n p : ℕ) (hp : (p : A) ∈ I)
    (a : A ⧸ I ^ (n + 2)) (ha : a ∈ RingHom.ker (transition (R := R) I n)) :
    (p : A ⧸ I ^ (n + 2)) * a = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have ha' : a ∈ I ^ (n + 1) := Ideal.Quotient.eq_zero_iff_mem.mp ha
  rw [← map_natCast (Ideal.Quotient.mk _) p, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  change (p : A) * a ∈ I ^ ((n + 1) + 1)
  rw [pow_succ']
  exact Ideal.mul_mem_mul hp ha'

/-- Powers by an integer in the ideal move points down its filtration. -/
theorem reduction_pow_pow_eq_one (I : Ideal A) (p : ℕ) (hp : (p : A) ∈ I)
    (x : Lie.AffinePoints G A)
    (hx : Lie.affineMap G (Ideal.Quotient.mkₐ R I) x = 1) (n : ℕ) :
    Lie.affineMap G (Ideal.Quotient.mkₐ R (I ^ (n + 1))) (x ^ (p ^ n)) = 1 := by
  induction n with
  | zero =>
    rw [show I ^ (0 + 1) = I by simp]
    simpa only [pow_zero, pow_one] using hx
  | succ n ih =>
    let y := Lie.affineMap G (Ideal.Quotient.mkₐ R (I ^ (n + 2))) (x ^ (p ^ n))
    have hy : Lie.affineMap G (transition I n) y = 1 := by
      rw [← Lie.affineMap_comp]
      exact ih
    have h := Lie.affineKernel_pow_eq_one G (transition I n)
      (transition_ker_sq I n) p (transition_ker_annihilated I n p hp) y hy
    simpa only [y, map_pow, pow_succ, pow_mul] using h

/-- A nilpotent identity kernel is killed uniformly by a power of any integer
belonging to the coefficient ideal. -/
theorem pow_eq_one (I : Ideal A) (p n : ℕ) (hp : (p : A) ∈ I)
    (hI : I ^ (n + 1) = ⊥) (x : Lie.AffinePoints G A)
    (hx : Lie.affineMap G (Ideal.Quotient.mkₐ R I) x = 1) :
    x ^ (p ^ n) = 1 := by
  have h := reduction_pow_pow_eq_one G I p hp x hx n
  apply (Lie.pointCoordinates G).injective
  have hc := congrArg (Lie.pointCoordinates G) h
  rw [Lie.pointCoordinates_naturality, ← map_one (Lie.affineMap G
    (Ideal.Quotient.mkₐ R (I ^ (n + 1)))), Lie.pointCoordinates_naturality] at hc
  apply AlgHom.ext
  intro a
  have ha := DFunLike.congr_fun hc a
  change Ideal.Quotient.mk (I ^ (n + 1)) _ = Ideal.Quotient.mk (I ^ (n + 1)) _ at ha
  rw [Ideal.Quotient.eq, hI, Ideal.mem_bot, sub_eq_zero] at ha
  exact ha

end Langlands.GroupScheme.NilpotentCoefficientPowers
