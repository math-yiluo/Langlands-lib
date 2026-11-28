import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicGroup

/-! # Compact Iwasawa factorization for an idempotent parabolic -/

namespace Langlands.HarmonicAnalysis

open UnitConjugation.IdempotentCentralizer

/-- For the upper triangular unit subgroup attached to any idempotent in a finite-dimensional
semisimple local algebra, there is a compact open subgroup giving the parabolic–compact
factorization of all ambient units. -/
def IdempotentParabolicIwasawaStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] (e : A) (he : IsIdempotentElem e),
    ∃ K : OpenSubgroup Aˣ, IsCompact (K : Set Aˣ) ∧
      ∀ g : Aˣ, ∃ p ∈ parabolicUnits F he, ∃ k ∈ K, g = p * k

end Langlands.HarmonicAnalysis
