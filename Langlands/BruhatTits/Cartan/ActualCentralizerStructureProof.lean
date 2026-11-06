import Langlands.BruhatTits.Cartan.ActualCentralizerSplitComponent
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Structure of the actual centralizer of a maximal split torus -/

universe u

namespace Langlands.BruhatTits.Cartan

open Langlands.GroupScheme

/-- The represented centralizer of a maximal split torus in a connected reductive group over a
field is connected reductive, and the torus is its split component. -/
theorem actualCentralizerStructure : ActualCentralizerStructureStatement.{u} :=
  actualCentralizerStructure_of genericCentralizer dynamicCentralizerReductive

end Langlands.BruhatTits.Cartan
