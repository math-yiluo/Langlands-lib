import Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof
import Langlands.AllField.Group.GL.BlockModulus
import Langlands.AllField.Group.GL.CompactOpen
import Langlands.AllField.Group.GL.UnramifiedCharacter
import Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement
/-!
# The normalized absolute value is one on an open subgroup of units

The one field-specific lemma of the p-adic module
`Langlands.Representation.Whittaker.MirabolicCompactTwistedPairingProof` that the
unequal-rank functional equation needs. For supplied data `T : LocalFieldData F`, the
normalized absolute value is one on an open subgroup of `Fˣ`. The field-generic
declarations of that module are used from the original, which this module imports. Its
main theorem, the one-dimensionality of the compact mirabolic twisted pairing, is not
ported.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicFunctionalMultiplicityStatement
open Langlands.AllField.Whittaker

open MeasureTheory
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.HarmonicAnalysis
open Langlands.Induction hiding SmoothRep
open Langlands.QuotientIntegration
open scoped ENNReal

universe uF

namespace MirabolicCompactTwistedPairing
open Langlands.Whittaker.MirabolicCompactTwistedPairing hiding isOpenNormOne_normalizedAbsoluteValue
open Langlands.AllField.Whittaker.MirabolicCompactTwistedPairing
open Langlands.Whittaker hiding MirabolicFunctionalMultiplicityStatement
open Langlands.AllField.Whittaker

section Generic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]

variable [T2Space F] [NonarchimedeanAddGroup F]
  [∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F)]
  [∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F)]

end Generic

/-- The normalized absolute value of supplied local-field data `T` is one on an open
subgroup of units. -/
theorem isOpenNormOne_normalizedAbsoluteValue {F : Type uF} [Field F]
    (T : LocalFieldData F) :
    letI := T.topology
    Shahidi.IsOpenNormOne (Langlands.AllField.RankinSelberg.normalizedAbsoluteValue T) := by
  let := T.topology
  have he : ((Shahidi.absUnits (Langlands.AllField.RankinSelberg.normalizedAbsoluteValue T)).ker : Set Fˣ) =
      T.normalizedAbsUnits.ker := by
    ext a
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    rw [← Units.val_inj, ← Units.val_inj, ← NNReal.coe_inj, ← NNReal.coe_inj]
    exact Iff.rfl
  rw [Shahidi.IsOpenNormOne, he]
  exact T.isOpen_ker_normalizedAbsUnits

end MirabolicCompactTwistedPairing

open Langlands.Whittaker.MirabolicCompactTwistedPairing hiding isOpenNormOne_normalizedAbsoluteValue
open Langlands.AllField.Whittaker.MirabolicCompactTwistedPairing

end Langlands.AllField.Whittaker
