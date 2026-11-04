import Langlands.GroupScheme.Torus.NoTorusUnipotentStatement
import Langlands.GroupScheme.Nilpotent.CentralTorusStatement
import Langlands.GroupScheme.Torus.FiniteFieldGeometricMaximalStatement
import Langlands.GroupScheme.Torus.AlgClosedTrivialMaximalUnipotentStatement
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmoothStatement
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSpanningStatement
import Langlands.GroupScheme.Lie.SemisimpleIsogenyReductionStatement

/-! # Statement: the structural inputs for no-torus unipotence -/

universe u

namespace Langlands.GroupScheme

/-- The exact arbitrary-field no-torus theorem follows from six explicit
structural inputs. This statement does not assert those inputs. -/
def NoTorusStructuralReductionStatement : Prop :=
  NilpotentCentralTorusStatement.{u} →
  FiniteFieldGeometricMaximalTorusStatement.{u} →
  AlgClosedTrivialMaximalTorusUnipotentStatement.{u} →
  Lie.SemisimpleCentralizerSmoothStatement.{u} →
  Lie.SemisimpleCentralizerSpanningStatement.{u} →
  SemisimpleIsogenyReductionStatement.{u} →
  NoTorusUnipotentStatement.{u}

end Langlands.GroupScheme
