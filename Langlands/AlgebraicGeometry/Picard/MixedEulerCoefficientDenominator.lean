import Langlands.AlgebraicGeometry.Picard.MixedLineBundleEuler
import Langlands.Algebra.RationalPolynomialNewtonIntegrality

/-! # Bounded denominators of actual mixed Euler coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

local instance (X : Scheme.{u}) : (structureSheaf X).IsQuasicoherent :=
  (LineBundle.trivial X).property.isQuasicoherent

local instance {X : Scheme.{u}} (N : LineBundle X) : N.obj.IsQuasicoherent :=
  N.property.isQuasicoherent

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- Actual twisted coherent Euler sequences take integer values. -/
theorem coherentEulerSequence_mem_intCast_range (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : LineBundle X) (n : ℕ) :
    coherentEulerSequence f M hM L n ∈ (Int.castRingHom ℚ).range :=
  ⟨_, rfl⟩

/-- Every coefficient of the actual mixed Euler polynomial with degree
truncation `d` has denominator dividing `d!`. -/
theorem factorial_mul_mixedLineBundleEulerPolynomial_coeff_mem (L N : LineBundle X)
    (d j : ℕ) :
    (d.factorial : ℚ) * (mixedLineBundleEulerPolynomial f L N d).coeff j ∈
      (Int.castRingHom ℚ).range :=
  Langlands.Algebra.RationalPolynomial.factorial_mul_coeff_newtonPolynomial_sub_mem _ _
    (coherentEulerSequence_mem_intCast_range f _ _ L)
    (coherentEulerSequence_mem_intCast_range f _ _ L) d j

/-- The actual mixed Euler coefficient with degree truncation `d` becomes an
integer after multiplication by `d!`. -/
theorem exists_int_factorial_mul_mixedLineBundleEulerCoefficient (L N : LineBundle X)
    (d : ℕ) :
    ∃ z : ℤ, (d.factorial : ℚ) * mixedLineBundleEulerCoefficient f L N d = z := by
  obtain ⟨z, hz⟩ := factorial_mul_mixedLineBundleEulerPolynomial_coeff_mem f L N d (d - 1)
  exact ⟨z, hz.symm⟩

end Langlands.AlgebraicGeometry.Picard
