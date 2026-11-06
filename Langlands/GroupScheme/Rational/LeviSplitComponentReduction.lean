import Langlands.GroupScheme.Rational.CharactersStatement
import Langlands.GroupScheme.Rational.LeviSplitComponentFactorization
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement

/-! # Reduction of the Levi split-component statement to dynamic centralizer reductivity -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Connected reductivity of closed representatives of dynamic centralizers implies
`LeviSplitComponentStatement`: its first conjunct is the instance of the hypothesis at the
cocharacter `groupHom μ ≫ i`, and its second conjunct is `leviSplitComponent_factorization`. -/
theorem leviSplitComponentStatement_of_dynamicCentralizerReductive
    (h : DynamicCentralizerReductiveStatement.{u}) : LeviSplitComponentStatement.{u} := by
  intro k _ G hG T i hT ν M j hjc hj
  have := hG.isAffineHom
  exact ⟨h k G hG _ M j hjc hj,
    fun _ _ hiG => leviSplitComponent_factorization hT ν hjc hj hiG⟩

end Langlands.GroupScheme
