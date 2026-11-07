import Langlands.Global.AdelicSpreadSmoothOpenStatement
import Langlands.AlgebraicGeometry.UniformLangWeilStatement

/-! # Conrad's Theorem 4.5 assuming only his Lemma 4.6 -/

universe u

namespace Langlands.Global

/-- Conrad's Theorem 4.5 in both characteristics, for arbitrary finite-type
spreads, assuming only the uniform Lang–Weil estimate of his Lemma 4.6. -/
def AdelicSpreadSmoothOpenOfLangWeilStatement : Prop :=
  Langlands.AlgebraicGeometry.UniformLangWeilStatement.{u} →
    AdelicSpreadSmoothOpenStatement.{u}

end Langlands.Global
