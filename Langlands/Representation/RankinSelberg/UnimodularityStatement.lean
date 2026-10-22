import Langlands.Representation.RankinSelberg.Measures

/-!
# Intrinsic right invariance of the normalized Haar measures

These propositions state the all-rank unimodularity obligations for the
existing general-linear and upper-unipotent Haar measures.
-/

namespace Langlands.RankinSelberg

universe uF

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The existing Haar measure on `GL_(n+1)(F)`, normalized on its integral
subgroup, is invariant under every right translation. -/
def GeneralLinearHaarRightInvariantStatement (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] : Prop :=
  MeasureTheory.Measure.IsMulRightInvariant (generalLinearHaar F n)

/-- The existing Haar measure on the actual upper-unipotent group `N_(n+1)(F)`,
normalized on its integral subgroup, is invariant under every right translation. -/
def UnipotentHaarRightInvariantStatement (n : ℕ)
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)] : Prop :=
  MeasureTheory.Measure.IsMulRightInvariant (unipotentHaar F n)

end Langlands.RankinSelberg
