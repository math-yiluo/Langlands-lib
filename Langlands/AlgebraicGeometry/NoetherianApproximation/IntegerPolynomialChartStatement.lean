import Mathlib.RingTheory.ZariskisMainTheorem

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- A quasi-finite polynomial chart at each maximal ideal in characteristic zero. -/
def IntegerPolynomialChartStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] (q : Ideal A) [q.IsMaximal],
    ∃ n : ℕ, ∃ f : MvPolynomial (Fin n) ℤ →ₐ[ℤ] A,
      Function.Injective f ∧
        letI := f.toRingHom.toAlgebra
        Algebra.QuasiFiniteAt (MvPolynomial (Fin n) ℤ) q

end Langlands.AlgebraicGeometry.NoetherianApproximation
