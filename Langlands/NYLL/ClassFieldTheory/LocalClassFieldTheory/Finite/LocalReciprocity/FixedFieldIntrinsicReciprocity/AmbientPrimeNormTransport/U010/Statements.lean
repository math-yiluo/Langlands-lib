/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 14 November 2026:
Extract only the asserted type of M283.010
relativeNorm_preimage_abstractRelativeFixedFieldUnit from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and package all original binders inside a closed Prop-valued
definition with the suffix Statement, preserving their order, binder kinds
and the source's universe-zero field type. The hypothesis hnorm, which the
conclusion does not mention, becomes an unnamed implication premise in its
source position. Write published names in full instead of using the source
namespace openings, and replace the source imports by the published modules
defining the objects named in the statement and Mathlib's
separable-closure module. Defer the truth proof; install
no instance or simp registration. Omit the original noncomputable section
and all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.IsSepClosed
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Relative.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions

/-!
# Relative norms of abstract relative fixed-field units: statement

A closed proposition saying that, over the separable closure of a field,
the class-formation relative norm of a unit of a relative fixed field,
transported back to the units of the smaller fixed field, is its ordinary
field norm.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Translating an abstract relative fixed-field unit through the fixed-field
unit equivalences sends its abstract relative norm to its ordinary field norm. -/
def relativeNorm_preimage_abstractRelativeFixedFieldUnitStatement : Prop :=
  ∀ (K : Type) [Field K]
    (H L : ClosedSubgroup Gal(SeparableClosure K/K))
    (hLH : L.toSubgroup ≤ H.toSubgroup)
    [Finite
      (H.toSubgroup ⧸
        Langlands.NYLL.CyclicCohomology.extensionSubgroup H L hLH)]
    [Finite
      ((Langlands.NYLL.ClassFormation.baseField
        Gal(SeparableClosure K/K)).toSubgroup ⧸
        Langlands.NYLL.CyclicCohomology.extensionSubgroup
          (Langlands.NYLL.ClassFormation.baseField Gal(SeparableClosure K/K))
          H (Langlands.NYLL.ClassFormation.le_baseField H))]
    (p : (abstractRelativeFixedField
      K (SeparableClosure K) hLH)ˣ)
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ),
    Langlands.NYLL.LocalFieldTheory.normUnits
        (abstractFixedField K (SeparableClosure K) H)
        (abstractRelativeFixedField K (SeparableClosure K) hLH)
        p =
      x →
      Additive.toMul
          ((abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H).symm
            (Langlands.NYLL.ClassFormation.relativeNorm
              (galoisAmbientUnitsRep K (SeparableClosure K))
              H L hLH
              (abstractRelativeFixedFieldUnitsEquivGaloisFixed
                K (SeparableClosure K) H L hLH
                  (Additive.ofMul p)))) =
        x

end Langlands.NYLL.LocalClassFieldTheory
