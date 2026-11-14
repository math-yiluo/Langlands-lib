import Langlands.Representation.Whittaker.MirabolicTwistedPairingRigidityProof
import Langlands.AllField.Representation.Derivative.MirabolicMinusIrreducibleProof
import Langlands.AllField.Representation.Derivative.MirabolicMinusPairingTransferProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankFrobeniusProof
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
import Langlands.AllField.Representation.Whittaker.MirabolicFunctionalMultiplicityProof
import Langlands.AllField.Representation.Whittaker.MirabolicPairingRigidityStepSupplement
/-!
# JPSS finite-spectral-exception mirabolic pairing rigidity

The proof of `MirabolicTwistedPairingRigidityStatement` in every rank: the
induction of `MirabolicPairingRigidityStep` with its three inputs supplied by the
published proofs of the two unnormalized `Φ⁻` statements and of functional
multiplicity.
-/

universe uF uV uW

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicCompactTwistedPairingStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement mirabolicFunctionalMultiplicity mirabolicTwistedPairingRigidity
open Langlands.AllField.Whittaker

/-- JPSS 1983, §1.5, Corollary 2: outside a finite set of spectral values
`q ^ (-s)`, a nonzero twisted bilinear form on two irreducible smooth mirabolic
representations forces both to be equivalent to the compact model. -/
theorem mirabolicTwistedPairingRigidity 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    MirabolicTwistedPairingRigidityStatement.{uF, uV, uW} F T n :=
  Langlands.AllField.Whittaker.MirabolicRigidity.mirabolicTwistedPairingRigidity_of_phiMinus F T
    (Langlands.AllField.Derivative.Mirabolic.phiMinusIrreducible F T)
    (Langlands.AllField.Derivative.Mirabolic.phiMinusIrreducible F T)
    (Langlands.AllField.Derivative.Mirabolic.phiMinusPairingTransfer F T)
    (mirabolicFunctionalMultiplicity F T) (mirabolicFunctionalMultiplicity F T) n

end Langlands.AllField.Whittaker
