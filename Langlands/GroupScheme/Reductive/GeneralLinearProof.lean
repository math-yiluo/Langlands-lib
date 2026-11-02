import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.GroupScheme.Reductive.GeneralLinearStatement

/-! # `GL_n` is reductive: proof -/

universe u

namespace Langlands.GroupScheme.GeneralLinear

/-- `GL_n` is connected reductive over every field and reductive over every commutative ring. -/
theorem reductiveStatement : ReductiveStatement.{u} :=
  ⟨fun k _ n _ _ => isConnectedReductive_generalLinear k n,
    fun n _ _ R => isReductive_generalLinear n R⟩

end Langlands.GroupScheme.GeneralLinear
