import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeNormalityStatement
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeNormalityReduction
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteProof
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureFiniteReduction
import Langlands.GroupScheme.Rational.FiniteFieldMaximalTorusTransporterReduction
import Langlands.GroupScheme.Rational.FiniteFieldSolvableEnvelopeNormalityProof
import Langlands.GroupScheme.Rational.FiniteFieldCentralCocharacterSolvableReduction
import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit
import Langlands.GroupScheme.Rational.RationalMaximalTorusDensityProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Normality of the fixed closed torus envelope over every field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over a finite field, a smooth connected affine group whose cocharacters are
all central has normal closed torus envelope: such a group is solvable. -/
private theorem finiteFieldCentralCocharacterEnvelopeNormality :
    FiniteFieldCentralCocharacterEnvelopeNormalityStatement.{u} := by
  intro k _ _ G _ _ _ hcentral
  exact finiteFieldSolvableEnvelopeNormality k G
    (finiteFieldCentralCocharacterSolvable_of parabolicDynamic finiteFieldQuasiSplit
      k G hcentral)

/-- Over every finite field, the fixed closed torus envelope commutes with base
change to the algebraic closure. -/
private theorem torusGeneratedEnvelopeAlgebraicClosureFinite :
    TorusGeneratedEnvelopeAlgebraicClosureFiniteStatement.{u} :=
  torusGeneratedEnvelopeAlgebraicClosureFinite_of maximalTorusBaseChange
    maximalTorusConjugacy
    (finiteFieldMaximalTorusTransporter_of finiteFieldCentralCocharacterEnvelopeNormality)

/-- CGP Proposition A.2.11: every actual representative of the fixed closed
envelope of all ground-field tori of a smooth connected affine group over any
field is normal on every relative test scheme. -/
theorem torusGeneratedEnvelopeNormality :
    TorusGeneratedEnvelopeNormalityStatement.{u} := by
  intro k _ G _ _ _ D
  obtain hfinite | hinfinite := finite_or_infinite k
  · exact D.isNormal_of_algebraicClosure_envelope_eq
      (torusGeneratedEnvelopeAlgebraicClosureFinite k G)
  · exact D.isNormal_of_algebraicClosure_envelope_eq
      (torusGeneratedEnvelopeAlgebraicClosureInfinite k G)

end Langlands.GroupScheme
