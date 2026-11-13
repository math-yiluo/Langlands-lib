import Langlands.Representation.Families.RenardGenericIrreducibilityReduction
import Langlands.Representation.Exponents.LeviInductionUnitarityProof
import Langlands.Representation.Exponents.LeviJacquetInductionSupercuspidalFiltrationProof
import Langlands.Representation.Exponents.LeviNormalizerQuotientProof

/-! # Renard VI.8.5 from its three remaining inputs

The published reduction `genericInducedIrreducibility_of_statements` derives Renard's
generic irreducibility theorem VI.8.5, `GenericInducedIrreducibilityStatement`, from eight
published statements. Five of them now have published or accompanying proofs:

* `LeviInductionAdmissibleStatement` and `LeviInductionUnitarizableStatement`, by
  `leviInductionAdmissible` and `leviInductionUnitarizable`
  (`Langlands.Representation.Exponents.LeviInductionUnitarityProof`);
* `LeviJacquetInductionSupercuspidalFiltrationStatement`, by
  `leviJacquetInductionSupercuspidalFiltration`;
* `LeviNormalizerFiniteQuotientStatement` and `LeviNormalizerNormFixingStatement`, by
  `leviNormalizerFiniteQuotient` and `leviNormalizerNormFixing`.

This module supplies those five proofs and keeps the other three as hypotheses: VI.8.4
(`InducedIrreducibilityOpenStatement`), Jacquet's theorem
(`RationalPointsIrreducibleAdmissibleStatement`) and unitarizability of supercuspidals with
unitary central character (`SupercuspidalUnitaryCentralCharacterUnitarizableStatement`),
also packaged as the proposition structure `GenericInducedIrreducibilityRemainingInputs`.
It does not prove the closed target.
-/

universe u v

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic

/-- **Renard VI.8.5** from VI.8.4, Jacquet's theorem and unitarizability of supercuspidal
representations with unitary central character. The other five inputs of
`genericInducedIrreducibility_of_statements` are discharged by published proofs. -/
theorem genericInducedIrreducibility_of_remainingStatements
    (hOpen : InducedIrreducibilityOpenStatement.{u, v})
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, v})
    (hSU : SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v}) :
    GenericInducedIrreducibilityStatement.{u, v} :=
  genericInducedIrreducibility_of_statements hOpen hAdm hSU leviInductionAdmissible
    leviInductionUnitarizable leviJacquetInductionSupercuspidalFiltration
    leviNormalizerFiniteQuotient leviNormalizerNormFixing

/-- The three inputs of Renard VI.8.5 that remain open: VI.8.4, Jacquet's theorem and
unitarizability of supercuspidal representations with unitary central character. They are
the first three fields of `GenericInducedIrreducibilityInputs`, at the same universes. -/
structure GenericInducedIrreducibilityRemainingInputs : Prop where
  inducedIrreducibilityOpen : InducedIrreducibilityOpenStatement.{u, v}
  irreducibleAdmissible : RationalPointsIrreducibleAdmissibleStatement.{u, v}
  supercuspidalUnitarizable : SupercuspidalUnitaryCentralCharacterUnitarizableStatement.{u, v}

/-- The three remaining inputs give all eight inputs of `genericInducedIrreducibility_of_inputs`;
the other five fields are filled by published proofs. -/
theorem genericInducedIrreducibilityInputs_of_remainingInputs
    (h : GenericInducedIrreducibilityRemainingInputs.{u, v}) :
    GenericInducedIrreducibilityInputs.{u, v} where
  inducedIrreducibilityOpen := h.inducedIrreducibilityOpen
  irreducibleAdmissible := h.irreducibleAdmissible
  supercuspidalUnitarizable := h.supercuspidalUnitarizable
  inductionAdmissible := leviInductionAdmissible
  inductionUnitarizable := leviInductionUnitarizable
  jacquetFiltration := leviJacquetInductionSupercuspidalFiltration
  normalizerFiniteQuotient := leviNormalizerFiniteQuotient
  normalizerNormFixing := leviNormalizerNormFixing

/-- **Renard VI.8.5** from the packaged remaining inputs. -/
theorem genericInducedIrreducibility_of_remainingInputs
    (h : GenericInducedIrreducibilityRemainingInputs.{u, v}) :
    GenericInducedIrreducibilityStatement.{u, v} :=
  genericInducedIrreducibility_of_remainingStatements h.inducedIrreducibilityOpen
    h.irreducibleAdmissible h.supercuspidalUnitarizable

end Langlands.Renard.AlgebraicFamily
