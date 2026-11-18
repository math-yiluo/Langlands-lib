import Langlands.AbelianScheme.IsogenyFinrankKernelCardStatement
import Langlands.AbelianScheme.IsogenyFinrankKernelCard

/-! # Proof that the degree of an isogeny in characteristic zero counts its kernel points -/

universe u

namespace Langlands.AbelianScheme

/-- `IsogenyFinrankKernelCardStatement` holds. -/
theorem isogenyFinrankKernelCard : IsogenyFinrankKernelCardStatement.{u} :=
  fun _ _ _ _ _ _ α hα y => IsogenyKernelCard.finrank_eq_natCard_ker α hα y

end Langlands.AbelianScheme
