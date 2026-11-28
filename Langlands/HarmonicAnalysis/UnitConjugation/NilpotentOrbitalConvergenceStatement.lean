import Langlands.Group.GL.LocalFieldTopology
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution

/-! # Convergence of nilpotent orbital integrals -/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- Each nilpotent element has a compatible quotient measure for which the orbital integrals
of all Schwartz–Bruhat functions converge absolutely. -/
def UnitConjugation.HasConvergentNilpotentOrbitalMeasures (A : Type v)
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [MeasurableSpace Aˣ] [BorelSpace Aˣ] :
    Prop :=
  ∀ N : A, IsNilpotent N →
    ∃ (_ : MeasurableSpace (LeftQuotient (conjugationCentralizer N)))
      (_ : BorelSpace (LeftQuotient (conjugationCentralizer N)))
      (μG : Measure Aˣ) (_ : μG.IsHaarMeasure)
      (μH : Measure (conjugationCentralizer N)) (_ : μH.IsHaarMeasure)
      (_ : μH.IsMulRightInvariant)
      (ν : Measure (LeftQuotient (conjugationCentralizer N))),
      IsCompatible (conjugationCentralizer N) μG μH ν ∧ OrbitalIntegralConverges N ν

/-- The existence and convergence of nilpotent orbital measures for `GL₁(A)` over a
nonarchimedean local field of characteristic zero, as used in Harish-Chandra's Lemma 3.3. -/
def LieAlgebraNilpotentOrbitalConvergenceStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    HasConvergentNilpotentOrbitalMeasures A

end Langlands.HarmonicAnalysis
