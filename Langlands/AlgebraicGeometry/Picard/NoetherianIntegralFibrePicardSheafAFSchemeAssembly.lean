import Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardPiecesReduction
import Langlands.AlgebraicGeometry.Picard.NoetherianAffineTestsPicardExtension
import Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsProof
import Langlands.AlgebraicGeometry.Picard.PicardHilbertPolynomialPiecesProof
import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralSheafClassTwistProof
import Langlands.AlgebraicGeometry.Picard.NoetherianOpenPiecesGluingProof

/-! # Assembly of the Picard scheme of an integral-fibre family over a noetherian ring

From representability of the Picard class sheaf on noetherian affine tests to representability
on all tests, and the remaining composition of the published prerequisite proofs, with the
Hilbert-pieces representability statement left as a hypothesis. -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Representability of the fppf Picard class sheaf on noetherian affine tests, by a scheme
locally of finite presentation with finite affine neighbourhoods, implies representability on
the whole slice by the same scheme. -/
theorem noetherianIntegralFibrePicardSheafAFScheme_of_noetherianAffineTests
    (h : NoetherianIntegralFibrePicardNoetherianTestsStatement.{u}) :
    NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u} := by
  intro R _ _ X f hprop hflat hint hsec hample
  obtain ⟨P, hPfp, hPaf, ⟨α⟩⟩ := h R X f hprop hflat hint hsec hample
  obtain ⟨ε, hε⟩ := hsec
  exact ⟨P, hPaf, NoetherianAffineTests.nonempty_representableBy_of_noetherianAffine f ε hε α⟩

/-- Representability on noetherian affine tests follows from the representability of the
Hilbert-polynomial pieces, by the published reduction and the published proofs of its other
four hypotheses. -/
theorem noetherianIntegralFibrePicardNoetherianTests_of_piecesRepresentability
    (hC : PicardHilbertPiecesRepresentabilityStatement.{u}) :
    NoetherianIntegralFibrePicardNoetherianTestsStatement.{u} :=
  noetherianIntegralFibrePicardPiecesReduction properAmpleClosedImmersionBySections
    picardHilbertPolynomialPieces hC properFlatIntegralSheafClassTwist noetherianOpenPiecesGluing

/-- The target statement follows from the representability of the Hilbert-polynomial pieces. -/
theorem noetherianIntegralFibrePicardSheafAFScheme_of_piecesRepresentability
    (hC : PicardHilbertPiecesRepresentabilityStatement.{u}) :
    NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u} :=
  noetherianIntegralFibrePicardSheafAFScheme_of_noetherianAffineTests
    (noetherianIntegralFibrePicardNoetherianTests_of_piecesRepresentability hC)

end Langlands.AlgebraicGeometry.Picard
