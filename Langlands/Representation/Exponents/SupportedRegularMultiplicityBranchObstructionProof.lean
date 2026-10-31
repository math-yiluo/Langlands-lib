import Langlands.Representation.Exponents.WeylBranchPiecesAssembly
import Langlands.Representation.Exponents.WeylBranchPieceLiftingFromUpper
import Langlands.Representation.Exponents.GeometricExcessBranchFromUpper
import Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentReduction
import Langlands.Representation.Exponents.ProductLeviCuspidalLocalizationProof
import Langlands.Representation.Geometric.GeometricLemmaProof

/-!
# The supported excess-multiplicity Weyl-branch obstruction

The two geometric-lemma pieces follow from the published geometric lemma, and
the cuspidal constituent piece follows from the product-Levi localization.
-/

namespace Langlands

universe uF uV uM uW

/-- The supported excess-multiplicity Weyl-branch obstruction, given the
product-Levi cuspidal localization at the two universe instances used. -/
theorem glSupportedRegularMultiplicityBranchObstruction_of_localization
    (hP2 : GLProductLeviCuspidalLocalizationStatement.{uF, uV, uM})
    (hP2' : GLProductLeviCuspidalLocalizationStatement.{uF, uV, uV}) :
    GLSupportedRegularMultiplicityBranchObstructionStatement.{uF, uV, uM, uW} :=
  glSupportedRegularMultiplicityBranchObstruction_of_pieces
    (glGeometricPieceLifting_of_upper Geometric.padicGeometricLemma)
    (glGeometricExcessBranch_of_upper Geometric.padicGeometricLemma)
    hP2
    (glCuspidalInductionJacquetConstituent_of_localization hP2')

/-- The supported excess-multiplicity Weyl-branch obstruction. -/
theorem glSupportedRegularMultiplicityBranchObstruction :
    GLSupportedRegularMultiplicityBranchObstructionStatement.{uF, uV, uM, uW} :=
  glSupportedRegularMultiplicityBranchObstruction_of_localization
    ProductLeviCuspidalLocalization.glProductLeviCuspidalLocalization
    ProductLeviCuspidalLocalization.glProductLeviCuspidalLocalization

end Langlands
