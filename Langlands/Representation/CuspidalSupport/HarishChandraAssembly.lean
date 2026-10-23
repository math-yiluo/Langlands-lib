import Langlands.Representation.CuspidalSupport.HarishChandraForwardProof
import Langlands.Representation.CuspidalSupport.HarishChandraConverseProof
import Langlands.Group.GL.CartanProof

namespace Langlands.CuspidalSupport

universe uF uV

/-- Harish-Chandra's compact-coefficient characterization on every product Levi. -/
theorem leviHarishChandraTheorem : LeviHarishChandraTheorem.{uF, uV} := by
  intro p _ F T n B
  let := T.topology
  intro A
  cases n with
  | zero => exact leviHarishChandraRankZero p F T B A
  | succ n =>
    exact ⟨HarishChandra.hasCompactSmoothDualCoefficients_of_isLeviQuasicuspidal_of_cartan
      GeneralLinear.Cartan.cartanDecomposition T B A.representation A.isSmooth,
      leviHarishChandraConverseTheorem p F T (n + 1) B A⟩

end Langlands.CuspidalSupport
