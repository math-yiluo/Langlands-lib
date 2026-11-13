import Langlands.Representation.Whittaker.MirabolicFunctionalMultiplicityProof
import Langlands.AllField.Representation.Smooth.SmallRealizationProof
import Langlands.AllField.Representation.Whittaker.MirabolicMinimalityProof
import Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement
/-!
# Functional multiplicity for irreducible mirabolic representations

JPSS (1983), Section 1.5, Corollary 1: for the mirabolic group over a nonarchimedean
local field with supplied data `T`,
the character-functional space of a smooth irreducible complex representation is at
most a line, and it is a line exactly when the representation is equivalent to the
compact standard model. The proof combines the Frobenius coefficient map with
compact minimality (BZ76, Proposition 5.15(c)) and countable-dimensional Schur.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicCompactMinimalityStatement MirabolicFunctionalMultiplicityStatement mirabolicCompactMinimality mirabolicFunctionalMultiplicity mirabolicFunctionalMultiplicity_canonical mirabolicFunctionalMultiplicity_of_minimality
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

section Generic

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ξ : Representation ℂ (mirabolic n F) V}

end Generic

section LocalField

/-- The target for every nonarchimedean local field `F` and every supplied
`T : LocalFieldData F`, from compact minimality. -/
theorem mirabolicFunctionalMultiplicity_of_minimality
    (hmin : MirabolicCompactMinimalityStatement.{uF})
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    MirabolicFunctionalMultiplicityStatement.{uF, uV} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanGroup (GeneralLinear (n + 1) F) :=
    Langlands.valuativeGeneralLinearNonarchimedean F (n + 1)
  let : LocallyCompactSpace (GeneralLinear (n + 1) F) :=
    T.generalLinearLocallyCompactSpace (n + 1)
  let : LocallyCompactSpace (mirabolic n F) := Mirabolic.locallyCompactSpace
  have : SecondCountableTopology (GeneralLinear (n + 1) F) :=
    T.generalLinearSecondCountableTopology (n + 1)
  have : SecondCountableTopology (mirabolic n F) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  intro ψ V _ _ ξ hξ hirr
  exact mirabolicFunctionalMultiplicity_of_generic ψ (hmin F T n ψ)
    (exists_mirabolicCompactEval_one_ne_zero ψ) hξ hirr
    (MirabolicRigidity.rank_le_aleph0 ξ hξ hirr)

end LocalField

/-- JPSS (1983), Section 1.5, Corollary 1, for the actual mirabolic group over every
nonarchimedean local field and every supplied topological datum. -/
theorem mirabolicFunctionalMultiplicity 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    MirabolicFunctionalMultiplicityStatement.{uF, uV} F T n :=
  mirabolicFunctionalMultiplicity_of_minimality mirabolicCompactMinimality F T n

end Langlands.AllField.Whittaker
