import Langlands.GroupScheme.Reductive.Basic
import Langlands.Shimura.Unitary.DeligneGroupScheme

/-! # The Deligne torus is reductive: statement -/

namespace Langlands.Shimura.DeligneTorus

/-- The real Deligne torus `𝕊 = Res_{ℂ/ℝ} 𝔾_m` is a connected reductive group over `ℝ`, and a
reductive group scheme over `Spec ℝ` in the sense of Conrad, Definition 3.1.1. -/
def ReductiveStatement : Prop :=
  GroupScheme.IsConnectedReductive groupScheme ∧ GroupScheme.IsReductive groupScheme

end Langlands.Shimura.DeligneTorus
