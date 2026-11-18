import Langlands.AbelianScheme.GeometricEndomorphismTraceComparisonStatement
import Langlands.AbelianScheme.GeometricDegreeTraceReduction
import Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialProof
import Langlands.AbelianScheme.IsogenyDegreeTateDeterminantNormReduction
import Langlands.AbelianScheme.IsogenyKernelCardTateDeterminantProof
import Langlands.AbelianScheme.TateDeterminantNonzeroSurjectiveProof
import Langlands.AbelianScheme.IsogenyFinrankKernelCard
import Langlands.AbelianScheme.FlatEqualDimensionQuasiFinite

/-! # The geometric endomorphism trace comparison -/

universe u

namespace Langlands.AbelianScheme

/-- The fixed rational geometric trace agrees with every actual prime Tate trace,
and the actual rational Tate modules have their finite geometric dimension. -/
theorem geometricEndomorphismTraceComparison :
    GeometricEndomorphismTraceComparisonStatement.{u} := by
  apply geometricDegreeTraceReduction endomorphismDegreeLinePolynomial
  apply isogenyDegreeTateDeterminantNormReduction
  · intro k _ _ _ A B α hα y
    exact IsogenyKernelCard.finrank_eq_natCard_ker α hα y
  · exact isogenyKernelCardTateDeterminant
  · exact tateDeterminantNonzeroSurjective
  · intro k _ _ A α hα
    exact SurjectiveIsogeny.isIsogeny_of_surjective α hα

end Langlands.AbelianScheme
