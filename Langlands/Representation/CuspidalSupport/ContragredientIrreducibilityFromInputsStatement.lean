import Langlands.Representation.CuspidalSupport.ContragredientIrreducibilityStatement
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement
import Langlands.Representation.Exponents.LeviJacquetContragredientStatement

/-! # Irreducibility and supercuspidality of contragredients from their remaining inputs

Renard 2026, VI.2.2, Corollary (printed p.140 / PDF p.146), states that a smooth
representation of `G(F)` is irreducible (resp. irreducible supercuspidal) if and only if
its smooth contragredient is. This module states that the published
`ContragredientIrreducibilityStatement` follows from two published statements that remain
unproved and are used in its proof: Jacquet's theorem (VI.2.2, Theorem) and the second
Theorem of VI.9.6. The implication is neither assumed nor proved here.
-/

universe u v

namespace Langlands.CuspidalSupport

/-- Renard VI.2.2, Corollary, holds for fields in universe `u` and carriers in `v`,
provided these hold: Jacquet's theorem that irreducible smooth representations of `G(F)`
with carriers in `v` are admissible, and the natural isomorphism
`r_{P̄}^G(π̃) ≅ (r_P^G π)~` of Renard VI.9.6 for carriers in `v`. -/
def ContragredientIrreducibilityFromInputsStatement : Prop :=
  Aubert.General.RationalPointsIrreducibleAdmissibleStatement.{u, v} →
  Aubert.General.RepresentedParabolic.LeviJacquetContragredientStatement.{u, v} →
  ContragredientIrreducibilityStatement.{u, v}

end Langlands.CuspidalSupport
