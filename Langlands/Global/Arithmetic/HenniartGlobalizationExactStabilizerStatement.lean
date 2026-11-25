import Langlands.Global.Arithmetic.HenniartGlobalizationStatement
import Langlands.Global.Arithmetic.HenniartGlobalizationReduction
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerStatement

/-!
# Henniart's relative globalization from Proposition 4.8 under the exact stabilizer condition

Henniart (2000), Théorème 3.1 and Sections 3.3–3.7, in the relative form
`RelativeGaloisGlobalization`, with Harris (1998), Proposition 4.8 taken in its
exact-stabilizer form `Harris.Proposition48ExactStabilizerStatement` (the auxiliary
character subject to Harris's condition (4.12) in the proof of Lemma 4.7). Two
proposition definitions: the counterpart of the published
`HenniartGlobalizationStatement`, and the counterpart of the published
`HenniartGlobalizationReductionStatement` with the same five local hypotheses. Each
implies its published counterpart (proved below). Neither statement is proved here.
-/

noncomputable section

set_option autoImplicit false

universe uK uQ uW uP

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Langlands.LocalFactor.CommonClosure Langlands.VirtualRepresentation
open Langlands.VirtualRepresentation.RelativeGlobal Langlands.Automorphic

/-- Henniart (2000), Sections 3.3–3.7, with Harris (1998), Proposition 4.8 in its
exact-stabilizer form: `Harris.Proposition48ExactStabilizerStatement` implies the
relative form of Théorème 3.1. This is `HenniartGlobalizationStatement` with
`Harris.Proposition48ExactStabilizerStatement` in place of
`Harris.Proposition48Statement`, at the same universes; the conclusion
`RelativeGaloisGlobalization` is unchanged. -/
def HenniartGlobalizationExactStabilizerStatement : Prop :=
  Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP} →
    RelativeGaloisGlobalization.{uK, uQ, uW, uP}

/-- Internal reduction, exact-stabilizer form: the existence of normalized local
reciprocity families, Tate's local restriction formula for induced reciprocity
representations, the central character comparison, the associated supercuspidal
induction and local transfer reciprocity imply
`HenniartGlobalizationExactStabilizerStatement`. This is
`HenniartGlobalizationReductionStatement` with the same five hypotheses, in the same
order and at the same universes, and with conclusion
`HenniartGlobalizationExactStabilizerStatement` in place of
`HenniartGlobalizationStatement`. -/
def HenniartGlobalizationExactStabilizerReductionStatement : Prop :=
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
    LocalInducedRestrictionStatement.{uW, 0} →
      AssociatedCentralCharacterStatement.{0, uW, uP} →
        AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP} →
          LocalTransferReciprocityStatement.{0} →
            HenniartGlobalizationExactStabilizerStatement.{uK, uQ, uW, uP}

/-- The exact-stabilizer globalization implies the published one, because
`Harris.Proposition48Statement` implies `Harris.Proposition48ExactStabilizerStatement`
(`Harris.proposition48ExactStabilizerStatement_of_proposition48Statement`). -/
theorem henniartGlobalizationStatement_of_exactStabilizer
    (h : HenniartGlobalizationExactStabilizerStatement.{uK, uQ, uW, uP}) :
    HenniartGlobalizationStatement.{uK, uQ, uW, uP} :=
  fun hHarris => h (Harris.proposition48ExactStabilizerStatement_of_proposition48Statement hHarris)

/-- The exact-stabilizer reduction implies the published reduction. -/
theorem henniartGlobalizationReductionStatement_of_exactStabilizer
    (h : HenniartGlobalizationExactStabilizerReductionStatement.{uK, uQ, uW, uP}) :
    HenniartGlobalizationReductionStatement.{uK, uQ, uW, uP} :=
  fun hccre hlir hacc hasi htransfer =>
    henniartGlobalizationStatement_of_exactStabilizer (h hccre hlir hacc hasi htransfer)

end Langlands.Global
