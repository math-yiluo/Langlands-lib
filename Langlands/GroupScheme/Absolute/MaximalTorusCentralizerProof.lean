import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # A maximal torus of a connected reductive group is its own centralizer -/

universe u

namespace Langlands.GroupScheme

/-- **Milne 17.84.** A maximal torus of a connected reductive group over any field is its own
centralizer, as an equality of subgroup functors on every test scheme. -/
theorem maximalTorusCentralizer : MaximalTorusCentralizerStatement.{u} :=
  maximalTorusCentralizer_of_structuralInputs dynamicCentralizerReductive noTorusUnipotent
    solvableTorusQuotient

end Langlands.GroupScheme
