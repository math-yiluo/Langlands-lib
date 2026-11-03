import Langlands.Representation.Aubert.General.RationalParabolicModulusStatement
import Langlands.BruhatTits.SpecialCompact.IwahoriHaarProductStatement
import Langlands.Representation.Aubert.General.RationalOppositeHaarReciprocityStatement
import Langlands.GroupScheme.Rational.Statement
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement
import Langlands.Analysis.Local.FiniteCoverCharacterStatement
import Langlands.Analysis.Local.ModularCharacterRegularityStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement

/-! # Structural inputs for the actual rational-parabolic modulus target -/

universe u

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.BruhatTits.SpecialCompact Langlands.Haar

/-- The actual common basis and Cartan comparison, torus Haar inputs, general
positive-character facts and dynamic-centralizer reductivity imply the original
ambient and parabolic modular-character target. -/
def RationalParabolicModulusAssemblyStatement : Prop :=
  IwahoriHaarProductStatement.{u} →
  RationalOppositeHaarReciprocityStatement.{u} →
  GenericCentralizerStatement.{u} →
  JointSpecialCompactBasisExistenceStatement.{u} →
  FiniteCoverCharacterStatement.{u} →
  ModularCharacterRegularityStatement.{u} →
  DynamicCentralizerReductiveStatement.{u} →
  RationalParabolicModulusStatement.{u}

end Langlands.Aubert.General.RationalPointFamily
