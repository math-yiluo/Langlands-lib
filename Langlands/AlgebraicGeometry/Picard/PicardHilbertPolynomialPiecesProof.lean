import Langlands.AlgebraicGeometry.Picard.PicardHilbertPolynomialPiecesReduction
import Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityProof
import Langlands.AlgebraicGeometry.Modules.ProperFibreCohomologyDimBaseChangeProof
import Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistCohomologyProof
import Langlands.AlgebraicGeometry.Modules.ProjectiveRelativeDivisorFibreHilbertProof

/-! # The Hilbert-polynomial pieces of the Picard functor: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- The Picard functor of a projective flat family with geometrically integral fibres over a
noetherian ring decomposes into open Hilbert-polynomial pieces. -/
theorem picardHilbertPolynomialPieces : PicardHilbertPolynomialPiecesStatement.{u} :=
  picardHilbertPolynomialPiecesReduction
    Modules.properFlatFibreCohomologySemicontinuity
    Modules.properFibreCohomologyDimBaseChange
    Modules.projectiveFibreTwistCohomology
    Modules.projectiveRelativeDivisorFibreHilbert

end Langlands.AlgebraicGeometry.Picard
