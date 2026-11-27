import Langlands.BushnellKutzko.DepthZeroShell
import Langlands.BushnellKutzko.FiniteMatrixGaussInjectivityProof

/-! # The lower bound by rank for the conductor of a supercuspidal class

An irreducible supercuspidal class of `GL_N(K)`, `N ≥ 2`, over a `p`-adic field `K` has
conductor at least `N`. The positive-level case is the higher-rank Swan formula; the depth-zero
case is the extreme determinant shell of the standard first-unit test function, which is nonzero
by injectivity of the finite matrix Gauss operator.
-/

namespace Langlands.BushnellKutzko

universe uK uV

/-- **Lower bound by rank for the supercuspidal conductor.** For every prime `p`, every
`K : PadicField p`, every `k : ℕ` and every irreducible supercuspidal class `π` of `GL_{k+2}(K)`,
the first fixed level `Henniart.Numerical.conductor K π` is at least `k + 2`. -/
theorem supercuspidalConductorRankLowerBound :
    SupercuspidalConductorRankLowerBoundStatement.{uK, uV} :=
  supercuspidalConductorRankLowerBound_of_nonzeroShell
    (standardDepthZeroShellNonzero_of_finiteMatrixGaussInjectivity
      finiteMatrixGaussInjectivity.{uK, uV})

end Langlands.BushnellKutzko
