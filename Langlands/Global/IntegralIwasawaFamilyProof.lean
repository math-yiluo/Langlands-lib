import Langlands.Global.IntegralIwasawaFamilyReduction
import Langlands.GroupScheme.IntegralModel.MaximalCompact

/-! # Existence of the almost-everywhere integral Iwasawa family -/

universe u

namespace Langlands.Global.IntegralIwasawaFamily

/-- Every number-field connected reductive group and actual parabolic admit
one integral Iwasawa family with all three properties of the original target. -/
theorem existenceStatement : ExistenceStatement.{u} :=
  existenceStatement_of_maximalCompact
    Langlands.GroupScheme.IntegralModel.maximalCompactStatement

end Langlands.Global.IntegralIwasawaFamily
