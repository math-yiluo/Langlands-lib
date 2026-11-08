import Langlands.Representation.Whittaker.GelfandGraev
import Langlands.Representation.Jacquet.Parabolic

/-!
# The Jacquet module of the Gelfand–Graev representation (statement)
-/

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open GeneralLinear Whittaker HarmonicAnalysis

universe uF

/-- The normalized Jacquet module of the Gelfand–Graev representation of `GL_(n+1)(F)` along a
standard block parabolic is equivalent to the Gelfand–Graev representation of the Levi, for the
canonical topology. -/
def GelfandGraevJacquetStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) (B : BlockShape (n + 1)),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    Nonempty ((F.canonicalTopologicalData.normalizedJacquet B (gelfandGraev ψ n)).Equiv
      (leviGelfandGraev B ψ.complex))

end Langlands.RankinSelberg.SupercuspidalCompleteness
