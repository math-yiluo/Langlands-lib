/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Extract the statements of M283.006 normUnits_mapEquiv and M283.007
normClass_mapEquiv from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
definitions without their proofs. Add the Langlands.NYLL namespace prefix
and the suffix Statement, refer to the published
Langlands.NYLL.LocalFieldTheory.normUnits and normClass by their full names,
and replace the source imports by the two published modules defining them.
Rename the hypotheses hcomm and h, which the propositions do not reference,
to _hcomm and _h to silence the unused-variable linter.
Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U005.Definitions

/-!
# Unit norms and norm classes under compatible field equivalences: statements

Closed propositions saying that unit norms, and equality of norm classes,
are transported by a pair of ring equivalences of the base and extension
fields that commute with the algebra maps.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Field norms on units commute with compatible ring equivalences of the
base and extension fields. -/
def normUnits_mapEquivStatement : Prop :=
  ∀ (F E F₀ E₀ : Type)
    [Field F] [Field E] [Field F₀] [Field E₀]
    [Algebra F E] [Algebra F₀ E₀]
    (phiF : F ≃+* F₀) (phiE : E ≃+* E₀)
    (_hcomm :
      RingHom.comp (algebraMap F₀ E₀) phiF.toRingHom =
        RingHom.comp phiE.toRingHom (algebraMap F E))
    (y : Eˣ),
    Langlands.NYLL.LocalFieldTheory.normUnits F₀ E₀
        (Units.mapEquiv phiE.toMulEquiv y) =
      Units.mapEquiv phiF.toMulEquiv
        (Langlands.NYLL.LocalFieldTheory.normUnits F E y)

/-- Compatible ring equivalences preserve equality of unit norm classes. -/
def normClass_mapEquivStatement : Prop :=
  ∀ (F E F₀ E₀ : Type)
    [Field F] [Field E] [Field F₀] [Field E₀]
    [Algebra F E] [Algebra F₀ E₀]
    (phiF : F ≃+* F₀) (phiE : E ≃+* E₀)
    (_hcomm :
      RingHom.comp (algebraMap F₀ E₀) phiF.toRingHom =
        RingHom.comp phiE.toRingHom (algebraMap F E))
    (a x : Fˣ)
    (_h : Langlands.NYLL.LocalFieldTheory.normClass F E a =
      Langlands.NYLL.LocalFieldTheory.normClass F E x),
    Langlands.NYLL.LocalFieldTheory.normClass F₀ E₀
        (Units.mapEquiv phiF.toMulEquiv a) =
      Langlands.NYLL.LocalFieldTheory.normClass F₀ E₀
        (Units.mapEquiv phiF.toMulEquiv x)

end Langlands.NYLL.LocalClassFieldTheory
