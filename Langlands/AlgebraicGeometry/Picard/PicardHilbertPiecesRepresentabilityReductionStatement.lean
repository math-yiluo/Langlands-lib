import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement
import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeStatement
import Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianStatement

/-! # Reduction of the representability of the Picard pieces to divisors, linear systems,
fppf quotients and base change of divisors -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Kleiman's construction of the quasi-projective pieces `P^φ_m` of the Picard scheme
(proof of Theorem 4.8, pp.29–31) as a reduction. Assume

* the scheme of relative effective divisors with its open Hilbert-polynomial pieces
  (`RelativeEffectiveDivisorHilbertPiecesStatement`, Kleiman Thm 3.7),
* the linear system of an invertible module on a proper flat family with geometrically
  integral fibres (`ProperFlatIntegralLinearSystemStatement`, Kleiman Thm 3.13),
* fppf quotients by flat proper equivalence relations on H-quasi-projective schemes, tested on
  locally noetherian schemes (`FppfQuotientLocallyNoetherianStatement`, Kleiman Lemma 4.9),
* base change of relative effective divisors and of their ideal sheaves
  (`RelativeEffectiveDivisorBaseChangeStatement`).

Then the pieces of the fppf Picard class sheaf cut out by the given opens are represented,
on locally noetherian test schemes, by H-quasi-projective schemes
(`PicardHilbertPiecesRepresentabilityStatement`). -/
def PicardHilbertPiecesRepresentabilityReductionStatement : Prop :=
  RelativeEffectiveDivisorHilbertPiecesStatement.{u} →
    ProperFlatIntegralLinearSystemStatement.{u} →
      FppfQuotientLocallyNoetherianStatement.{u} →
        RelativeEffectiveDivisorBaseChangeStatement.{u} →
          PicardHilbertPiecesRepresentabilityStatement.{u}

end Langlands.AlgebraicGeometry.Picard
