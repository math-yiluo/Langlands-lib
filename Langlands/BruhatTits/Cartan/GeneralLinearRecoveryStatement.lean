import Langlands.Geometry.Building.DepthZero.GeneralLinearStatement
import Langlands.BruhatTits.SpecialCompact.GeneralLinearIntegralCartanStatement

/-! # Recovering the `GL_N` Cartan decomposition from the general Cartan theorem

`GeneralLinearCartanRecoveryStatement` is the reduction of the concrete Cartan bijection for
`GL_N(𝒪[F])` (`SpecialCompact.GeneralLinearIntegralCartanStatement`) to the identification of
the vertex parahorics of `GL_N` with the conjugates of `GL_N(𝒪[F])`
(`Geometry.Building.GeneralLinearVertexParahoricStatement`). The mathematical route combines
the premise with two theorems, the general Cartan theorem for one datum
(`parahoricCartanConclusions_of_satisfiesGroupAxioms`) and the existence of building data
(`Geometry.Building.groupAxiomsExistence`); neither is a premise. This definition states the
reduction and does not prove it.
-/

universe u

namespace Langlands.BruhatTits.Cartan

/-- **The concrete `GL_N` Cartan decomposition from the general theorem.** If, for every
nonarchimedean local field `F`, every `N` and all building data of `GL_N` over `F` satisfying
the one-group axioms, the vertex parahorics are exactly the `G(F)`-conjugates of
`GL_N(𝒪[F])`, then the positive uniformizer points of the diagonal torus represent the
`GL_N(𝒪[F])`-double cosets of `GL_N(F)` bijectively, for every generic cocharacter. -/
def GeneralLinearCartanRecoveryStatement : Prop :=
  Geometry.Building.GeneralLinearVertexParahoricStatement.{u} →
    SpecialCompact.GeneralLinearIntegralCartanStatement.{u}

end Langlands.BruhatTits.Cartan
