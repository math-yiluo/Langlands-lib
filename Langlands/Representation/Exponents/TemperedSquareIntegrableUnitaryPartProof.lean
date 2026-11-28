import Langlands.Representation.Exponents.SelfUnitaryPieceMultiplicityUnconditional
import Langlands.Representation.Exponents.TemperedSquareIntegrableUnitaryPartStatement
import Langlands.Representation.Exponents.CasselmanNecessity
import Langlands.Representation.Exponents.CasselmanSufficiencyReduction
import Langlands.Representation.Exponents.TemperedPositiveJacquetExponents
import Langlands.Representation.Exponents.TemperedCentralCharacterData
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Square-integrability of tempered representations through unitary Jacquet parts

Renard 2026, VII.2.4, Lemma (printed p.230 / PDF p.236). The forward direction is
the necessity half of Casselman's criterion together with the comparison, for
tempered representations, between strictly positive exponents and vanishing unitary
Jacquet parts. The reverse direction is the sufficiency half of Casselman's
criterion, which the Library derives from the Bruhat–Tits theorem
`Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.4, Lemma, from the sufficiency half of Casselman's criterion at the
same field and carrier universes. The forward direction uses no premise. -/
theorem temperedSquareIntegrableUnitaryPart_of_casselmanSufficiency
    (hS : ArbitraryParabolicCasselmanSufficiencyStatement.{u, v}) :
    TemperedSquareIntegrableUnitaryPartStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  let := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ _ _ haar _ π ω hπ hω
  have := hG.smooth
  constructor
  · exact unitaryJacquetPart_eq_bot_of_tempered_squareIntegrable G hG haar π hπ
  · intro hvan
    exact hS k G hG haar π hπ.isAdmissible ⟨hπ.unitaryCentralCharacter hω⟩
      ((hasPositiveRepresentedJacquetExponents_iff_unitaryJacquetParts_vanish hG π hπ).2 hvan)

/-- **Renard VII.2.4, Lemma.** Let `G` be a connected reductive group over a
nonarchimedean local field, with `G(F)` locally compact and nonarchimedean, and fix
a Haar measure on `G(F) ⧸ Z(G(F))`. A normalized-exponent tempered representation
of `G(F)` on which the center acts by a character is square integrable modulo the
center if and only if its unitary Jacquet part vanishes at every actual rational
parabolic that is not an isomorphism, for every rational Levi, matching geometric
unipotent radical and split component. -/
theorem temperedSquareIntegrableUnitaryPart :
    TemperedSquareIntegrableUnitaryPartStatement.{u, v} :=
  temperedSquareIntegrableUnitaryPart_of_casselmanSufficiency
    (arbitraryParabolicCasselmanSufficiency_of_jointSpecialCompactBasis
      BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence)

end Langlands.Aubert.General.RepresentedParabolic
