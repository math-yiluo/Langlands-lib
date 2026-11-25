import Langlands.Representation.Archimedean.RealReverseInduced
import Langlands.Representation.Archimedean.RealTieClasses
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction

/-!
# Intertwiners to the reversed standard module

`realReverseIntertwinerKernel` proves `RealReverseIntertwinerKernelStatement` (module
`RealStandardIrreducibleCriterionReduction`): every `(𝔤, K)`-intertwiner from a Langlands-ordered
real standard module to the standard module of the reversed list of blocks vanishes on every
proper `(𝔤, K)`-submodule. The proof cuts the list into its tie classes (`RealTieClasses`) and
applies `RealReverseInduced.reverseKernel` along the standard parabolic subgroup whose diagonal
blocks are the classes. The nonvanishing of the limit pairing used there is
`realLeviWitness` (module `RealLeviWitness`).

The result is conditional on three inputs, passed as hypotheses: the
two analytic statements `RealLeviChartIntegrableStatement` and
`RealLeviParabolicIntegrationStatement` used by the limit along that parabolic subgroup, and
irreducibility of standard modules with constant real exponent
(`RealTemperedStandardIrreducibleStatement`).
-/

noncomputable section

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealReverseIntertwinerKernel

open RealLeviChart RealLeviSlices RealInducedStandardBound RealTieClasses RealReverseInduced

/-- **Intertwiners to the reversed standard module**, conditional on the two analytic statements
of the limit along a standard parabolic subgroup and irreducibility of standard modules with
constant real exponent. -/
theorem realReverseIntertwinerKernel (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement)
    (htemp : RealTemperedStandardIrreducibleStatement) :
    RealReverseIntertwinerKernelStatement := by
  intro n ds T W hN hord hT hW hWne
  obtain ⟨c, dss, rfl, hanti, hstrict, hX⟩ := exists_tieData htemp ds hord
  have hn : n = ∑ j, sz dss j := hN.symm.trans (realRank_flat dss)
  subst hn
  exact reverseKernel hT1 hT3 hanti hstrict hX T hT W hW hWne

end RealReverseIntertwinerKernel

open RealLeviChart RealReverseIntertwinerKernel in
/-- **Reduction of the reverse-intertwiner statement.** The two analytic statements of the limit
along a standard parabolic subgroup and irreducibility of standard modules with constant real
exponent imply `RealReverseIntertwinerKernelStatement`. -/
def RealReverseIntertwinerKernelReductionStatement : Prop :=
  RealLeviChartIntegrableStatement → RealLeviParabolicIntegrationStatement →
    RealTemperedStandardIrreducibleStatement → RealReverseIntertwinerKernelStatement

theorem realReverseIntertwinerKernelReduction : RealReverseIntertwinerKernelReductionStatement :=
  fun hT1 hT3 htemp =>
    RealReverseIntertwinerKernel.realReverseIntertwinerKernel hT1 hT3 htemp

end Langlands.Archimedean
