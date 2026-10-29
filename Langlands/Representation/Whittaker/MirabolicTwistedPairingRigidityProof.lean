import Langlands.Representation.Whittaker.MirabolicPairingRigidityStep
import Langlands.Representation.Derivative.MirabolicMinusIrreducibleProof
import Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof
import Langlands.Representation.Whittaker.MirabolicFunctionalMultiplicityProof

/-!
# JPSS finite-spectral-exception mirabolic pairing rigidity

The proof of `MirabolicTwistedPairingRigidityStatement` in every rank: the
induction of `MirabolicPairingRigidityStep` with its three inputs supplied by the
published proofs of the two unnormalized `Φ⁻` statements and of functional
multiplicity.
-/

universe uF uV uW

namespace Langlands.Whittaker

/-- JPSS 1983, §1.5, Corollary 2: outside a finite set of spectral values
`q ^ (-s)`, a nonzero twisted bilinear form on two irreducible smooth mirabolic
representations forces both to be equivalent to the compact model. -/
theorem mirabolicTwistedPairingRigidity {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    MirabolicTwistedPairingRigidityStatement.{uF, uV, uW} F T n :=
  MirabolicRigidity.mirabolicTwistedPairingRigidity_of_phiMinus F T
    (Derivative.Mirabolic.phiMinusIrreducible F T)
    (Derivative.Mirabolic.phiMinusIrreducible F T)
    (Derivative.Mirabolic.phiMinusPairingTransfer F T)
    (mirabolicFunctionalMultiplicity F T) (mirabolicFunctionalMultiplicity F T) n

end Langlands.Whittaker
