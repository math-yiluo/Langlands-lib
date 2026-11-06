import Langlands.Representation.Exponents.LeviJacquetContragredientStatement
import Langlands.Representation.Exponents.UniformCompressionStabilizationStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessStatement
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement

/-! # Jacquet modules of contragredients from their remaining inputs

Renard 2026, VI.9.6, second Theorem (VI.9.6.2) (printed p.201 / PDF p.207), proves
`r_{P̄}^G π̃ ≅ (r_P^G π)~` through the Proposition of VI.9.6 (printed pp.202–205 /
PDF pp.208–211), using the uniform stabilization of VI.9.1 and the structure of
parabolics. This module states that the published `LeviJacquetContragredientStatement`
follows from the published statements that remain unproved and are used in that proof.
The implication is neither assumed nor proved here.
-/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The second Theorem of Renard VI.9.6 holds for fields in universe `u` and carriers in
`v`, provided these hold: the dynamic description of parabolics; uniqueness of the opposite
dynamic parabolic with a given Levi; uniform stabilization (VI.9.1) for carriers in `v`; and
reciprocity of the adjoint determinants of `U(ζ)` and `U(-ζ)`. -/
def LeviJacquetContragredientFromInputsStatement : Prop :=
  ParabolicDynamicStatement.{u} →
  OppositeDynamicParabolicUniquenessStatement.{u} →
  RationalPointFamily.UniformCompressionStabilizationStatement.{u, v} →
  Dynamic.LeviAdjointDeterminantReciprocityStatement.{u} →
  LeviJacquetContragredientStatement.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
