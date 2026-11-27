import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomialComparisonStatement
import Langlands.AlgebraicGeometry.Picard.MumfordRosatiMixedEulerTraceReduction

/-! # Comparing twisted Euler polynomials from eventual square equality -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter Polynomial

universe u

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AbelianScheme.Rosati.MumfordTraceReduction (euler_facts)

/-- Eventual agreement of squared twisted Euler characteristics determines the twisted
Euler polynomial by the positive leading coefficients. -/
theorem coherentEulerPolynomial_eq_of_eventually_sq_eq
    : CoherentEulerPolynomialSquareComparisonStatement.{u} := by
  intro K K' _ _ X X' p p' _ _ g h h' hc hc' L N L' N' hL hL' hsq
  let leftPolynomial := coherentEulerPolynomial p N.obj (hasFiniteAffineSections_lineBundle N) L g
  let rightPolynomial :=
    coherentEulerPolynomial p' N'.obj (hasFiniteAffineSections_lineBundle N') L' g
  obtain ⟨he, ht, -⟩ := euler_facts p g h L N
  obtain ⟨he', ht', -⟩ := euler_facts p' g h' L' N'
  have hpoly : leftPolynomial ^ 2 = rightPolynomial ^ 2 := by
    apply Langlands.Algebra.RationalPolynomial.eq_of_eventually_nat_eval_eq
    filter_upwards [hsq] with n hn
    simpa only [leftPolynomial, rightPolynomial, eval_pow, he n, he' n] using hn
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hpoly with hp | hp
  · exact hp
  · have hpos := lineBundleEulerPolynomial_topCoeff_pos p g h hc L hL
    have hpos' := lineBundleEulerPolynomial_topCoeff_pos p' g h' hc' L' hL'
    have heq := congrArg (fun Q : ℚ[X] => Q.coeff g) hp
    change (coherentEulerPolynomial p N.obj (hasFiniteAffineSections_lineBundle N) L g).coeff g =
      (-(coherentEulerPolynomial p' N'.obj (hasFiniteAffineSections_lineBundle N') L' g)).coeff g
      at heq
    rw [coeff_neg, ht, ht'] at heq
    linarith

end Langlands.AlgebraicGeometry.Picard
