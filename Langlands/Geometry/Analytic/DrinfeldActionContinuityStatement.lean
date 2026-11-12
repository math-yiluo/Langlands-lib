import Langlands.Geometry.Analytic.DrinfeldGroupAction
import Mathlib.Topology.Instances.Matrix

/-! # Statement: continuity of the action of `GL_{d+1}(F)` on Drinfeld's upper half space -/

universe u v

namespace Langlands.Analytic.DrinfeldUpperHalfSpace

/-- Statement: for a locally compact nonarchimedean field `F`, a complete ultrametric normed
`F`-algebra `K` that is a field, and `d ≥ 1`, the action of `GL_{d+1}(F)` (with the topology of
the units of the matrix algebra) on Drinfeld's upper half space `Ω` over `K` is continuous in
Berkovich's sense. -/
def OmegaActionContinuityStatement : Prop :=
  ∀ (F : Type v) [NontriviallyNormedField F] [ProperSpace F]
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [NormedAlgebra F K] (d : ℕ) [NeZero d],
    SaturatedAtlasPresentation.IsContinuousAction (omegaAction F K d).ρAut

end Langlands.Analytic.DrinfeldUpperHalfSpace
