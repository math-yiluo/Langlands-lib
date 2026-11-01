import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement

/-! # Connectedness of the actual two-power torsion closure -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

universe u

/-- The Zariski closure of the actual geometric two-power torsion locus is
connected. -/
def TwoPowerTorsionClosureConnectedStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (A : AbelianScheme (Spec (CommRingCat.of K))),
    _root_.IsConnected (closure (twoPowerTorsionLocus A))

end Langlands.AbelianScheme.Tate
