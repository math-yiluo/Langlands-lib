import Langlands.GroupScheme.Reductive.LinearlyReductiveInvariantFiniteGenerationStatement
import Langlands.GroupScheme.Reductive.LinearlyReductiveInvariantIntegral
import Langlands.GroupScheme.Reductive.PolynomialInvariantAverage
import Langlands.GroupScheme.Reductive.InvariantPolynomialAlgebra
import Langlands.Algebra.GradedReynoldsFiniteGeneration
import Mathlib.RingTheory.Polynomial.Basic

/-! # Hilbert finite generation for linearly reductive group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open MatrixRepresentation CoordinateIntegration

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Hilbert's theorem, with all-test invariance over an arbitrary field. -/
theorem linearlyReductiveInvariantFiniteGeneration :
    LinearlyReductiveInvariantFiniteGenerationStatement.{u} := by
  intro k _ G _ _ hss n ρ
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let I := invariantIntegralOfLinearReductivity G hss
  apply (ρ.invariantPolynomialSubalgebra_fg_iff).mp
  refine Langlands.Algebra.subalgebra_fg_of_graded_reynolds
    ρ.invariantPolynomialSubalgebra (MvPolynomial.homogeneousSubmodule (Fin n) k)
    (PolynomialAverage.reynolds ρ I)
    (fun F => PolynomialAverage.reynolds_invariant ρ I F)
    (fun F hF => PolynomialAverage.reynolds_eq_self ρ I hF)
    (fun s hs F => PolynomialAverage.reynolds_mul ρ I hs F)
    (fun d F hF => ρ.invariantPolynomialSubalgebra_proj_mem d F hF) ?_
  intro F hF
  rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at hF
  exact hF

end Langlands.GroupScheme
