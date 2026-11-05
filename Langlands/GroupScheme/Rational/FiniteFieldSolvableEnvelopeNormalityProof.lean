import Langlands.GroupScheme.Rational.FiniteFieldSolvableEnvelopeNormalityStatement
import Langlands.GroupScheme.Rational.EnvelopeKernelCentralizerAssembly
import Langlands.GroupScheme.Rational.SmoothTorusGeneratedEnvelope
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.Rational.FiniteFieldSplitUnipotentProductProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Torus-envelope normality for solvable groups over finite fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every finite field, the fixed closed torus envelope of a smooth
connected affine solvable group is normal on every relative test scheme. -/
theorem finiteFieldSolvableEnvelopeNormality :
    FiniteFieldSolvableEnvelopeNormalityStatement.{u} := by
  intro k _ _ G _ _ _ hG
  let D := smoothTorusGeneratedEnvelope G
  let : Smooth D.group.X.hom := smoothTorusGeneratedEnvelope_smooth G
  let : ConnectedSpace D.group.X.left :=
    smoothTorusGeneratedEnvelope_connectedSpace G
  let a := perfectFieldSectionedSolvableTorusQuotient solvableTorusQuotient
    RelativeRoot.splitUnipotentStableVectorSubgroup G hG
  exact D.isNormal_of_finiteField_sectionedQuotient
    RelativeRoot.splitUnipotentStableVectorSubgroup
    RelativeRoot.finiteFieldSplitUnipotentProduct a
    (D.sectionedQuotientKernelCentralizerGeometry a)

end Langlands.GroupScheme
