import Langlands.AlgebraicGeometry.NoetherianApproximation.FiniteIterateFrobeniusStatement
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- An iterate of Frobenius on a finite type integer algebra is a finite ring map. -/
theorem finite_iterateFrobenius (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (p n : ℕ) [ExpChar R p] : (iterateFrobenius R p n).Finite := by
  have hint : (iterateFrobenius R p n).IsIntegral := by
    intro x
    refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C x (ne_of_gt (expChar_pow_pos R p n)), ?_⟩
    simp [iterateFrobenius_def]
  have hcomp :
      (iterateFrobenius R p n).comp (algebraMap ℤ R) = algebraMap ℤ R := by
    ext
    simp
  exact hint.to_finite <| RingHom.FiniteType.of_comp_finiteType <|
    hcomp.symm ▸ RingHom.finiteType_algebraMap.mpr inferInstance

theorem finiteIterateFrobenius : FiniteIterateFrobeniusStatement :=
  finite_iterateFrobenius

end Langlands.AlgebraicGeometry.NoetherianApproximation
