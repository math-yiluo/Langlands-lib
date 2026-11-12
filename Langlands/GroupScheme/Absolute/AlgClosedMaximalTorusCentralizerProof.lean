import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # algClosedMaximalTorusCentralizer: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- A maximal torus of a connected reductive group over an algebraically closed field equals its full all-test centralizer. -/
theorem algClosedMaximalTorusCentralizer :
    AlgClosedMaximalTorusCentralizerStatement.{u} :=
  algClosedMaximalTorusCentralizerReduction dynamicCentralizerReductive
    noTorusUnipotent solvableTorusQuotient

end Langlands.GroupScheme
