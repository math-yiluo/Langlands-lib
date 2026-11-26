import Langlands.Global.AdelicEisensteinRegularParameterStatement
import Langlands.Global.AdelicEisensteinRegularRegion

/-! # Nonemptiness of the Eisenstein regular-parameter region -/

universe u

open AlgebraicGeometry

namespace Langlands.Global

/-- Connected reductivity supplies the finite-type hypothesis for the regular-region lemma. -/
theorem eisensteinRegularParameter : EisensteinRegularParameterStatement.{u} := by
  intro F _ G P M A _ p l a r _ _ _ hA hT hG R
  let : Smooth G.X.hom := hG.smooth
  exact r.exists_regularParameter hA hT R

end Langlands.Global
