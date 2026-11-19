import Langlands.GroupScheme.Reductive.PicardTrivialInnerFormAssembly
import Langlands.GroupScheme.Reductive.RelativeQuasiSplitInnerFormProof
import Langlands.GroupScheme.RelativeLevi.AdjointTorusWeilPresentationProof
import Langlands.GroupScheme.Adjoint.RelativeExistenceProof
import Langlands.GroupScheme.RelativeUnipotent.RadicalFiltrationProof
import Langlands.Algebra.IntegerFiniteEtalePicard
import Langlands.Algebra.AffineSpaceFiniteEtalePicardReduction
import Langlands.Algebra.AffineSpaceFiniteEtalePolynomialProductProof

/-! # Proof: quasi-split inner forms over bases with trivial Picard groups

The published assembly `reductivePicardTrivialQuasiSplitInnerFormStatement_of_prerequisites`
derives the target from four relative geometric inputs, the Picard triviality of finite étale
algebras over rings isomorphic to `ℤ`, and the Picard triviality of finite étale algebras over
affine spaces in characteristic zero. All six inputs are proved in the Library; this module
supplies them. -/

universe u

namespace Langlands.GroupScheme

/-- **Quasi-split inner forms over `Spec ℤ`, affine spaces and bases with trivial Picard
groups** (Conrad, *Reductive group schemes* (2014), Remark 7.2.13). -/
theorem reductivePicardTrivialQuasiSplitInnerFormStatement :
    ReductivePicardTrivialQuasiSplitInnerFormStatement.{u} :=
  reductivePicardTrivialQuasiSplitInnerFormStatement_of_prerequisites
    relativeQuasiSplitInnerFormExistence.{u}
    relativeAdjointQuotientExistence.{u}
    relativeUnipotentRadicalFiltration.{u}
    relativeBorelAdjointTorusWeilPresentation.{u}
    (fun R _ h => Langlands.Algebra.finiteEtaleAlgebrasHaveTrivialPicard_of_ringEquiv_int.{u, u} R h)
    (Langlands.Algebra.affineSpaceFiniteEtalePicardTrivial_of_polynomialProduct
      Langlands.Algebra.affineSpaceFiniteEtalePolynomialProduct.{u})

end Langlands.GroupScheme
