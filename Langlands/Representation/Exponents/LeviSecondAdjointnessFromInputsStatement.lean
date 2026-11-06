import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement
import Langlands.Representation.Exponents.UniformCompressionStabilizationStatement
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessStatement
import Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement
import Langlands.GroupScheme.Rational.StandardCocharacterStatement

/-! # Bernstein's second adjointness from its remaining inputs

Renard 2026, VI.9.6, first Theorem (VI.9.6.1) (printed p.201 / PDF p.207), proves
`r_{P̄}^G` right adjoint to `i_P^G` (printed pp.201–205 / PDF pp.207–211) using the
uniform stabilization of VI.9.1, the contragredient of an induced representation (III.2.7)
and the structure of parabolics.
This module states that the published `LeviSecondAdjointnessStatement` follows from the
published statements that remain unproved and are used in that proof.
The implication is neither assumed nor proved here.
-/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.9.6 (VI.9.6.1) holds for fields in universe `u` and carriers in
`max u v`, provided these hold: the dynamic description of parabolics; uniqueness of the
opposite dynamic parabolic with a given Levi; uniform stabilization (VI.9.1) for carriers in
`max u v`; reciprocity of the adjoint determinants of `U(ζ)` and `U(-ζ)`; unimodularity of
reductive groups with the standard-cocharacter statement it uses; and compactness of parabolic
quotients. -/
def LeviSecondAdjointnessFromInputsStatement : Prop :=
  ParabolicDynamicStatement.{u} →
  OppositeDynamicParabolicUniquenessStatement.{u} →
  RationalPointFamily.UniformCompressionStabilizationStatement.{u, max u v} →
  Dynamic.LeviAdjointDeterminantReciprocityStatement.{u} →
  RationalPointFamily.RationalReductiveUnimodularityStatement.{u} →
  StandardCocharacterStatement.{u} →
  ArbitraryParabolicQuotientCompactStatement.{u} →
  LeviSecondAdjointnessStatement.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
