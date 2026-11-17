import Langlands.GroupScheme.Torus.MultiplicativeTypeQuasiIsotrivialReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypePointwiseSplitting

/-! # Groups of multiplicative type are quasi-isotrivial -/

universe u

namespace Langlands.GroupScheme

/-- **Quasi-isotriviality of groups of multiplicative type** (Conrad, B.3.4). A group of
multiplicative type splits over an étale cover of its base, and over a henselian local base
it splits over a finite étale surjective cover. -/
theorem multiplicativeTypeQuasiIsotrivial : MultiplicativeTypeQuasiIsotrivialStatement.{u} :=
  MultiplicativeTypeQuasiIsotrivial.multiplicativeTypeQuasiIsotrivial_of_pointwise
    fun _ _ hH s => hH.exists_etale_diagonalizable s

end Langlands.GroupScheme
