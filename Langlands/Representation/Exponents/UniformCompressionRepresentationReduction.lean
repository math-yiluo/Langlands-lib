import Langlands.Representation.Exponents.UniformCompressionNativeAssembly
import Langlands.Representation.Exponents.ArbitraryParabolicFiniteSupportReduction
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetStructuralReduction
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicIntersectionCentralizerProof
import Langlands.GroupScheme.Rational.ParabolicDoubleCosetAssembly
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Uniform dynamic compression from the remaining representation inputs

The published structural theorems discharge eight of the thirteen inputs of
`uniformCompressionStabilization_of_nativeStatements`. The five remaining
representation-theoretic statements stay premises.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Plancherel CuspidalSupport

universe u v uV

/-- Compactness of every literal represented-parabolic quotient, from the
published dynamic description of parabolics and dynamic quotient compactness. -/
theorem arbitraryParabolicQuotientCompact_of_dynamicTheorems :
    RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement.{u} := by
  intro k _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ P p hp
  exact RepresentedParabolic.compactSpace_leftQuotient_pointImage_of_dynamic
    parabolicDynamic BruhatTits.dynamicParabolicQuotientCompact hG p hp

/-- Native Jacquet fixed-module finiteness for the actual universal induced
supercuspidal family, from the published structural reduction and the
published structural theorems. -/
theorem rationalSupercuspidalJacquetFamilyFinite_of_structuralTheorems :
    RationalSupercuspidalJacquetFamilyFiniteStatement.{u, uV} :=
  rationalSupercuspidalJacquetFamilyFinite_of_structural
    (representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs
      rationalBruhat genericMinimalParabolic minimalParabolicConjugacy
      parabolicIntersectionCentralizer parabolicDynamic smoothMaximalSplitTorusConjugacy)
    arbitraryParabolicQuotientCompact_of_dynamicTheorems

/-- The five representation-theoretic Library statements that remain inputs
of the native assembly imply the unchanged uniform endpoint. This proposition
does not assert any of its inputs. -/
def UniformCompressionRepresentationReductionStatement : Prop :=
  RationalPointsIrreducibleAdmissibleStatement.{u, max u v} →
  RationalCuspidalInertiaProductDecompositionStatement.{u, max u v} →
  RationalCuspidalInertiaFinitenessStatement.{u, max u v} →
  RationalUniversalSmallProgeneratorStatement.{u, max u v} →
  RationalCuspidalInducedEmbeddingStatement.{u, max u v} →
  UniformCompressionStabilizationStatement.{u, v}

/-- The published structural theorems and the proved native Jacquet finiteness
discharge eight inputs of the native assembly; the other five stay premises. -/
theorem uniformCompressionStabilization_of_representationStatements
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, max u v})
    (hDecomp : RationalCuspidalInertiaProductDecompositionStatement.{u, max u v})
    (hFinite : RationalCuspidalInertiaFinitenessStatement.{u, max u v})
    (hGen : RationalUniversalSmallProgeneratorStatement.{u, max u v})
    (hEmbed : RationalCuspidalInducedEmbeddingStatement.{u, max u v}) :
    UniformCompressionStabilizationStatement.{u, v} :=
  uniformCompressionStabilization_of_nativeStatements
    genericMinimalParabolic parabolicDynamic smoothMaximalSplitTorusConjugacy
    standardCocharacter standardLeviIntersection relativeRootSystem
    BruhatTits.dynamicParabolicQuotientCompact hAdm
    rationalSupercuspidalJacquetFamilyFinite_of_structuralTheorems
    hDecomp hFinite hGen hEmbed

/-- The conditional reduction holds at arbitrary independent universes. -/
theorem uniformCompressionRepresentationReduction :
    UniformCompressionRepresentationReductionStatement.{u, v} :=
  uniformCompressionStabilization_of_representationStatements

end Langlands.Aubert.General.RationalPointFamily
