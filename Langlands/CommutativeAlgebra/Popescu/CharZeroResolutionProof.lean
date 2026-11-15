import Langlands.CommutativeAlgebra.Popescu.CharZeroResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.CharZeroResolutionAssembly
import Langlands.CommutativeAlgebra.Popescu.NilpotentLiftingProof
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardDesingularizationProof
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardSmoothProof
import Langlands.CommutativeAlgebra.Popescu.DimZeroResolutionProof
import Langlands.CommutativeAlgebra.Popescu.CharZeroFieldFactorizationProof
import Langlands.CommutativeAlgebra.Popescu.RegularSequenceFlat
import Langlands.CommutativeAlgebra.Popescu.RegularParameterChoiceProof
import Langlands.CommutativeAlgebra.Popescu.StrictlyStandardRetractProof

/-! # Stacks Lemma 10.3 (07FE) in characteristic zero -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks, *Smoothing Ring Maps*, Lemma 10.3 (Tag 07FE), characteristic-zero case: for a field
`k` of characteristic zero, a `k`-algebra map `f : A → Λ` from a finite type `k`-algebra to a
Noetherian `k`-algebra, and a prime `q` of `Λ` minimal over `h_A Λ` with `Λ_q` regular, the
situation `(k → A → Λ, q)` can be resolved. -/
theorem charZeroResolution : CharZeroResolutionStatement.{u} :=
  charZeroResolution_of NilpotentLifting.nilpotentLifting Desing.strictlyStandardDesingularization
    strictlyStandardSmooth dimZeroResolution charZeroFieldFactorization regularSequenceFlat
    regularParameterChoice strictlyStandardRetract

end Langlands.CommutativeAlgebra.Popescu
