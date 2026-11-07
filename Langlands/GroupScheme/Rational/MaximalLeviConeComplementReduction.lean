import Langlands.GroupScheme.Rational.MaximalLeviCentralKernel
import Langlands.GroupScheme.Rational.MaximalLeviConeComplementLine

/-! # The missed-direction statement from the dynamic description of parabolics -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- If every parabolic subgroup is a dynamic parabolic, then a nonzero real character that
vanishes on the central directions and misses both positive cones determines the parabolics
with a given maximal Levi. -/
def MaximalLeviConeComplementFromParabolicDynamic : Prop :=
  ParabolicDynamicStatement.{u} → MaximalLeviConeComplementStatement.{u}

/-- The reduction of `MaximalLeviConeComplementStatement` to `ParabolicDynamicStatement`. -/
theorem maximalLeviConeComplementFromParabolicDynamic :
    MaximalLeviConeComplementFromParabolicDynamic.{u} := fun hPD =>
  MaximalLeviConeComplementLine.maximalLeviConeComplement_of_line
    fun _ _ _ hG _ _ _ _ _ _ hp hl hpp hmax ha _ hx0 hx =>
      mem_span_of_hasCentralKernelCharacter ha.1.1.1
        (hasCentralKernelCharacter_of_maximal hPD hG hp hl hpp hmax ha) hx0 hx

end Langlands.GroupScheme
