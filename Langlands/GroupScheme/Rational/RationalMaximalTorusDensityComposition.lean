import Langlands.GroupScheme.Rational.MaximalTorusParameterExistenceStatement
import Langlands.GroupScheme.Rational.MaximalTorusParameterUnirationalStatement
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalDensityExtension

/-! # The density deduction from the maximal-torus parameter propositions -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The two unrestricted parameter propositions imply the exact conjugator-density
proposition. The parameter propositions remain premises of this auxiliary result. -/
def RationalMaximalTorusDensityCompositionStatement : Prop :=
  MaximalTorusParameterExistenceStatement.{u} →
    MaximalTorusParameterUnirationalStatement.{u} →
      RationalMaximalTorusConjugateDensityStatement.{u}

/-- Smooth base change, rational density on the same parameter scheme and the
published conjugator-density reduction give the exact density conclusion. -/
theorem rationalMaximalTorusConjugateDensity_of_parameter_statements
    (hexists : MaximalTorusParameterExistenceStatement.{u})
    (hunirational : MaximalTorusParameterUnirationalStatement.{u}) :
    RationalMaximalTorusConjugateDensityStatement.{u} := by
  intro k _ _ G _ _ _ T₀ j₀ hj₀
  obtain ⟨Q, q, hparameter⟩ := hexists k G T₀ j₀ hj₀
  let : Smooth ((Over.pullback (toAlgebraicClosure k)).map q).left :=
    MorphismProperty.overPullbackMap (P := @Smooth)
      (toAlgebraicClosure k) q hparameter.smooth_map
  have hdense : HasDenseRationalPoints k Q :=
    (hunirational k G T₀ j₀ hj₀ Q q hparameter).hasDenseRationalPoints
  exact dense_torusConjugators_of_parameters j₀ q
    ((Over.pullback (toAlgebraicClosure k)).map q).left.isOpenMap
    hparameter.conjugationCompatible
    (hasDenseGeometricRationalPoints_of_hasDenseRationalPoints
      (K := AlgebraicClosure k) Q hdense)

/-- The packaged conditional composition is proved by the preceding deduction. -/
theorem rationalMaximalTorusDensityComposition :
    RationalMaximalTorusDensityCompositionStatement.{u} :=
  rationalMaximalTorusConjugateDensity_of_parameter_statements

end Langlands.GroupScheme
