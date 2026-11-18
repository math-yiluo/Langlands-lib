import Langlands.Correspondence.HenniartPolarPart
import Langlands.Correspondence.HenniartRefinedStrata

namespace Langlands.Henniart

universe uK uV

/-- Input (I1) of Option II in the numerical local Langlands route note.
The cardinality of the refined supercuspidal orbit stratum is bounded by the
polar-part count at the residue cardinality of `K`. -/
def SupercuspidalStratumUpperBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k s f : ℕ),
    (Numerical.supercuspidalRefinedStratum.{uK, uV} K k s f).encard ≤
      (Numerical.polarPartCount K.canonicalTopologicalData.residueCardinality
        (k + 1) f s : ℕ∞)

end Langlands.Henniart
