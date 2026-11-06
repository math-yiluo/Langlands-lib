import Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs
import Langlands.Representation.Exponents.ArbitraryParabolicQuotientCompactStatement
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement

/-! # Renard VII.1.3 from its remaining inputs

Renard 2026, VII.1.3 (PDF pp.230–232) proves the reducibility criterion for inductions
from irreducible supercuspidal representations of maximal Levis using results of Chapters
III–VI. This module states that the published `MaximalLeviSupercuspidalReducibilityStatement`
follows from the published statements that remain unproved and are used in that proof.
The implication is neither assumed nor proved here.
-/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.1.3 holds for fields in universe `u` and representation carriers of the
Levi in universe `v`, provided these hold: the dynamic description of parabolics;
admissibility of irreducible representations (for carriers in `v` and in `max u v`);
compactness of parabolic quotients; unimodularity of reductive groups with the
standard-cocharacter statement it uses; existence of root presentations of parabolics;
unitarizability of supercuspidals with unitary central character; and the three
maximal-Levi inputs on endomorphisms, morphisms and unitarizable constituents of
`i_P^G ρ`. -/
def MaximalLeviSupercuspidalReducibilityFromInputsStatement : Prop :=
  ParabolicDynamicStatement.{u} →
  RationalPointsIrreducibleAdmissibleStatement.{u, v} →
  RationalPointsIrreducibleAdmissibleStatement.{u, max u v} →
  ArbitraryParabolicQuotientCompactStatement.{u} →
  RationalPointFamily.RationalReductiveUnimodularityStatement.{u} →
  StandardCocharacterStatement.{u} →
  ParabolicRootPresentationExistenceStatement.{u} →
  SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v} →
  MaximalLeviSupercuspidalInductionEndomorphismStatement.{u, v} →
  MaximalLeviSupercuspidalInductionHomStatement.{u, v} →
  MaximalLeviSupercuspidalUnitarizableConstituentStatement.{u, v} →
  MaximalLeviSupercuspidalReducibilityStatement.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
