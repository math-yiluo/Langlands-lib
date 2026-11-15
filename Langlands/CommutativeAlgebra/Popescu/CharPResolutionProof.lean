import Langlands.CommutativeAlgebra.Popescu.CharPResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.CharPResolutionAssembly
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardSmoothProof
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardRetractProof
import Langlands.CommutativeAlgebra.Popescu.AnnihilatorStabilizationProof
import Langlands.CommutativeAlgebra.Popescu.RegularLocalParametersProof
import Langlands.CommutativeAlgebra.Popescu.RegularSequencePowersProof
import Langlands.CommutativeAlgebra.Popescu.ArtinianSmoothApproximationProof
import Langlands.CommutativeAlgebra.Popescu.SequenceDimZeroResolutionProof

/-! # Stacks Lemma 16.11.4 (Tag 07FJ): resolution of the local problem in characteristic `p` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.11.4 (07FJ): in characteristic `p > 0`, `k → A → Λ ⊃ q` can be resolved
when `Λ` is geometrically regular over `k` and `q` is minimal over `h_A`. -/
theorem charPResolution : CharPResolutionStatement.{u} :=
  CharP.charPResolution_of strictlyStandardSmooth strictlyStandardRetract
    annihilatorStabilization regularLocalParameters regularSequencePowers
    artinianSmoothApproximation sequenceDimZeroResolution

end Langlands.CommutativeAlgebra.Popescu
