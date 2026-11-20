import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Statement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.GlobalGenerationReductionStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.GeneratedEffectiveRealization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceRefinementSections
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceInduction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceMatchingGluingProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.LaurentInductionProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.BinaryLaurentSplitProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.SplitSquareGenerationProof

/-! # Effective finite Banach affinoid algebra descent along finite full-domain covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

namespace FiniteAffinoidAlgebraDescent

/-- Generation of matching families from generation of the restricted pieces
on the members of a finite cover. -/
theorem pieceMatchingLocalGeneration : PieceMatchingLocalGenerationStatement.{u} := by
  intro K _ _ _ R c F t V e n s hs
  exact PieceRefinement.generates_of_piecesGenerate t e s hs

end FiniteAffinoidAlgebraDescent

/-- A finite matching tuple generating every original local algebra gives an
effective realization. -/
theorem finiteAffinoidAlgebraGlobalGenerationReduction :
    FiniteAffinoidAlgebraGlobalGenerationReductionStatement.{u} := by
  intro K _ _ _ R c F d n s hs
  exact ⟨FiniteAffinoidAlgebraDescent.effectiveRealizationOfGenerators d s hs⟩

/-- Every finite matching datum has a finite matching tuple generating every
original local algebra. -/
theorem finiteAffinoidAlgebraGlobalGeneration :
    FiniteAffinoidAlgebraGlobalGenerationStatement.{u} :=
  FiniteAffinoidAlgebraDescent.globalGeneration_of_prerequisites
    FiniteAffinoidAlgebraDescent.pieceMatchingLocalGeneration
    FiniteAffinoidAlgebraDescent.pieceMatchingGluing
    finiteCoverBinaryLaurentInduction
    domainBinaryLaurentSplitSquare
    BoundedAlgHom.splitSquareModuleGeneration

/-- Effective finite Banach affinoid algebra descent along every finite
full-domain cover. -/
theorem finiteAffinoidAlgebraDescent : FiniteAffinoidAlgebraDescentStatement.{u} := by
  intro K _ _ _ R c F d
  obtain ⟨n, s, hs⟩ := finiteAffinoidAlgebraGlobalGeneration K R c F d
  exact finiteAffinoidAlgebraGlobalGenerationReduction K R c F d n s hs

end Langlands.Analytic.PresentedAffinoidAlgebra
