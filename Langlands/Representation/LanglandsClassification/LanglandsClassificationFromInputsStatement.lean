import Langlands.Representation.LanglandsClassification.LanglandsClassificationStatement
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement
import Langlands.Representation.Exponents.LeviInductionFiniteLengthStatement
import Langlands.Representation.Exponents.LeviJacquetFiniteLengthStatement
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleStatement

/-! # The Langlands classification from its remaining inputs

Renard 2026, VII.4.2, Theorem (printed p.243 / PDF p.249, proof to printed p.246 / PDF
p.252). This module states that the published `LanglandsClassificationStatement` follows
from four published statements that the proof uses and the Library does not yet prove:
second adjointness (VI.9.6), finite length of normalized induction (VI.6.2) and of
normalized Jacquet modules (VI.6.4), and Jacquet's theorem that irreducible smooth
representations are admissible (VI.2.2). The implication is neither assumed nor proved
here.
-/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VII.4.2 holds for fields in universe `u` and carriers in `v`, provided these hold:
second adjointness for represented parabolics (carriers in `max u v`), preservation of finite
length by normalized induction and by normalized Jacquet functors (carriers in `v`), and
admissibility of irreducible smooth representations of `G(F)` (carriers in `v`). -/
def LanglandsClassificationFromInputsStatement : Prop :=
  LeviSecondAdjointnessStatement.{u, v} →
  LeviInductionFiniteLengthStatement.{u, v} →
  RationalPointsIrreducibleAdmissibleStatement.{u, v} →
  LeviJacquetFiniteLengthStatement.{u, v} →
  LanglandsClassificationStatement.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
