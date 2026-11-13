import Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardNoetherianTestsStatement
import Langlands.AlgebraicGeometry.Picard.NoetherianOpenPiecesGluingStatement
import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.PicardHilbertPolynomialPiecesStatement
import Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsStatement
import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralSheafClassTwistStatement

/-! # The Picard scheme on noetherian affine tests from its Hilbert-polynomial pieces -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Suppose that

* a proper scheme over a noetherian affine base with an ample line bundle has an invertible
  module whose sections give a closed immersion into a finite projective space;
* the Picard functor of a projective flat family with geometrically integral fibres decomposes
  into open Hilbert-polynomial pieces;
* each such piece is represented on locally noetherian tests by an H-quasi-projective scheme;
* fppf Picard classes of a pointed proper flat family with geometrically integral fibres are
  classes of line bundles, modulo pullbacks from the base;
* a Zariski sheaf with such quasi-projective open pieces is represented on noetherian affine
  tests by a scheme with finite affine neighbourhoods.

Then the fppf Picard class sheaf of a pointed proper flat family with geometrically integral
fibres and an ample line bundle over a noetherian ring is represented on noetherian affine tests
by a scheme locally of finite presentation with finite affine neighbourhoods. -/
def NoetherianIntegralFibrePicardPiecesReductionStatement : Prop :=
  ProperAmpleClosedImmersionBySectionsStatement.{u} →
    PicardHilbertPolynomialPiecesStatement.{u} →
      PicardHilbertPiecesRepresentabilityStatement.{u} →
        ProperFlatIntegralSheafClassTwistStatement.{u} →
          NoetherianOpenPiecesGluingStatement.{u} →
            NoetherianIntegralFibrePicardNoetherianTestsStatement.{u}

end Langlands.AlgebraicGeometry.Picard
