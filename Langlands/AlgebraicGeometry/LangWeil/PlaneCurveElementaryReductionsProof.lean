import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveElementaryReductionsStatement
import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveLinearFibres

/-!
# Elementary plane-curve reductions

The exact elementary-reductions interface follows from Frobenius contraction,
coordinate exchange, induction on the degree sum, and counting linear fibres.
-/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

theorem planeCurveElementaryReductions : PlaneCurveElementaryReductionsStatement.{u} := by
  constructor
  · intro F _ _ f hirr hx hy
    exact planeCurve_separable_model f hirr hx hy
  · intro F _ _ f hirr hf
    exact planeCurve_linear_zero_count_error f hirr hf

end Langlands.AlgebraicGeometry.LangWeil
