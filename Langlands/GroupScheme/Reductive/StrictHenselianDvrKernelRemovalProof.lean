import Langlands.AlgebraicGeometry.HenselianFinitePart
import Langlands.GroupScheme.Reductive.HenselianKernelRemoval

/-! # Closed-fibre kernel removal over a strictly Henselian DVR -/

universe u

namespace Langlands.GroupScheme

/-- Remove the finite closed-fibre part of a fibrewise-isogeny kernel over a
strictly Henselian discrete valuation ring. -/
theorem strictHenselianDvrKernelRemoval :
    StrictHenselianDvrKernelRemovalStatement.{u} := by
  apply strictHenselianDvrKernelRemoval_of_henselianFinitePart
  intro R _ _ X f _ _ _ _
  exact ⟨(Langlands.AlgebraicGeometry.HenselianFinitePart.finitePart f).1,
    (Langlands.AlgebraicGeometry.HenselianFinitePart.finitePart f).2⟩

end Langlands.GroupScheme
