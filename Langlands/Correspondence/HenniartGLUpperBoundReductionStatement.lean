import Langlands.BushnellKutzko.SupercuspidalClassMaximalTypeStatement
import Langlands.BushnellKutzko.SupercuspidalClassTypeInvariantsStatement
import Langlands.BushnellKutzko.SupercuspidalClassConjugateTypeTwistStatement
import Langlands.BushnellKutzko.GLMaximalSimpleTypeLabelBoundStatement
import Langlands.Correspondence.HenniartGLUpperBoundStatement

/-!
# The supercuspidal stratum upper bound from maximal simple types

Input (I1) of Option II of the numerical local Langlands route note,
`SupercuspidalStratumUpperBoundStatement`, stated as a consequence of four statements on
maximal simple types: their existence in every supercuspidal class (BK93 (8.4.1)), the
torsion number and Swan exponent they determine (BK93 (6.2.5), BK94 (3.10)(i)), the unramified twists
relating classes that contain conjugate types (BK93 (6.2.3)), and the labelling of their
conjugacy classes (BK94 (3.7)–(3.8)). The argument is Remark `rem:upper` of the route note.
Proposition definition only.
-/

namespace Langlands.Henniart

/-- The four Bushnell–Kutzko inputs together imply input (I1): every supercuspidal class
contains a maximal simple type (`SupercuspidalClassMaximalTypeStatement`); such a type fixes
the torsion number and the Swan exponent of the class
(`SupercuspidalClassTypeInvariantsStatement`); classes containing conjugate types are
unramified twists of each other (`SupercuspidalClassConjugateTypeTwistStatement`); and the
maximal simple types have labels such that equal labels imply conjugacy, with `e(p) = 1`
in positive depth (`GLMaximalSimpleTypeLabelBoundStatement`). Then the refined supercuspidal
orbit stratum `S_K(k + 1, s, f)` has at most `polarPartCount q (k + 1) f s` elements, `q` the
residue cardinality of `K` (`SupercuspidalStratumUpperBoundStatement`). The types have
carriers in the universe `uT`. -/
def SupercuspidalStratumUpperBoundReductionStatement.{uK, uV, uT} : Prop :=
  BushnellKutzko.SupercuspidalClassMaximalTypeStatement.{uK, uV, uT} →
  BushnellKutzko.SupercuspidalClassTypeInvariantsStatement.{uK, uV, uT} →
  BushnellKutzko.SupercuspidalClassConjugateTypeTwistStatement.{uK, uV, uT} →
  BushnellKutzko.GLMaximalSimpleTypeLabelBoundStatement.{uK, uT} →
  SupercuspidalStratumUpperBoundStatement.{uK, uV}

end Langlands.Henniart
