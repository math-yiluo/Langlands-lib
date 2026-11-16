import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreReduction
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChange
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobal
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStep

/-! # Murre's criterion for unramified functors

Bourbaki exp. 294 (Murre), Theorem 1 in the form of its Corollary 1, sufficiency direction:
over a locally noetherian scheme `S`, a presheaf on `Over S` satisfying Murre's conditions
is represented by a scheme that is separated, locally of finite type and formally unramified
over `S`. The theorem combines the three steps of the proof (stability of the conditions
under base change, Murre's Proposition 2, and the local step of the induction) through the
reduction `murreCriterion_of_steps`. -/

universe u v

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

/-- Murre's criterion (Bourbaki exp. 294, Theorem 1 / Corollary 1, sufficiency direction). -/
theorem murreCriterion : MurreCriterionStatement.{u, v} :=
  murreCriterion_of_steps ⟨murreBaseChange, murreLocalToGlobal, murreLocalStep⟩

end Langlands.AlgebraicGeometry.UnramifiedFunctor
