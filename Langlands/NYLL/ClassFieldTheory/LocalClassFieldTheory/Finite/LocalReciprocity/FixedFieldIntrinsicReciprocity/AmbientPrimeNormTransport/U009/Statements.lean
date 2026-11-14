/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 14 November 2026:
Extract only the asserted type of M283.009
relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and package all original binders inside a closed Prop-valued
definition with the suffix Statement, preserving their order, binder kinds
and the source's universe-zero field type. Write published names in full
instead of using the source namespace openings, and replace the source
imports by the published modules defining the objects named in the
statement. Defer the truth proof; install no instance or simp registration.
Omit the original noncomputable section and all other declarations of the
module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions

/-!
# Relative norms from the intrinsic base to a fixed field: statement

A closed proposition saying that, under the canonical identifications of
units of fixed fields of the separable closure with Galois-fixed units, the
class-formation relative norm from a closed subgroup of finite index up to
the full absolute Galois group is the ordinary field norm on units.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Under the canonical fixed-field unit identifications, the abstract
relative norm from an intrinsic fixed field is the ordinary field norm on
units. -/
def relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnitStatement :
    Prop :=
  ∀ (F : Type) [Field F]
    (S : ClosedSubgroup Gal(SeparableClosure F/F))
    (hSB : S.toSubgroup ≤ (intrinsicAbstractBase F).toSubgroup)
    [Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        Langlands.NYLL.CyclicCohomology.extensionSubgroup
          (intrinsicAbstractBase F) S hSB)]
    [FiniteDimensional F
      (abstractFixedField F (SeparableClosure F) S)]
    (p : (abstractFixedField F (SeparableClosure F) S)ˣ),
    Langlands.NYLL.ClassFormation.relativeNorm (intrinsicAbsoluteUnits F)
        (intrinsicAbstractBase F) S hSB
        (abstractFixedFieldUnitsEquivGaloisFixed
          F (SeparableClosure F) S (Additive.ofMul p)) =
      baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)
        (Additive.ofMul
          (Langlands.NYLL.LocalFieldTheory.normUnits F
            (abstractFixedField F (SeparableClosure F) S) p))

end Langlands.NYLL.LocalClassFieldTheory
