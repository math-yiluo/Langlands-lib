import Langlands.GroupScheme.Torus.MultiplicativeTypeNormalIsotrivialAssembly
import Langlands.AlgebraicGeometry.EtaleLocalSystemLevelStructure
import Langlands.Algebra.FiniteOrderCongruenceProof
import Langlands.AlgebraicGeometry.FiniteLocallyConstantRepresentableProof
import Langlands.AlgebraicGeometry.EtaleLocalSystemIsotrivialSpreadingProof

/-! # Groups of multiplicative type over normal bases are locally isotrivial -/

universe u

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry in
/-- A group of multiplicative type over a normal scheme splits over finite étale
covers Zariski-locally, and over a single finite étale cover if the base is irreducible. -/
theorem multiplicativeTypeNormalIsotrivial :
    MultiplicativeTypeNormalIsotrivialStatement.{u} :=
  multiplicativeTypeNormalIsotrivial_of_localSystem
    (EtaleLocalSystem.etaleLocalSystemNormalIsotrivial_of
      Langlands.FiniteOrderCongruence.finiteOrderCongruenceDetection
      finiteLocallyConstantRepresentable
      etaleLocalSystemIsotrivialSpreading)

end Langlands.GroupScheme
