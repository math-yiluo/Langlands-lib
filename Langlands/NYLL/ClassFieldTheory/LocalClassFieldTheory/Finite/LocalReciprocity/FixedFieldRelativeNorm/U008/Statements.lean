/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 14 November 2026:
Extract only the asserted type of M276.008
relativeNorm_abstractFixedFieldUnit_eq_normUnits from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldRelativeNorm.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Package the theorem's complete telescope, including the section variables
it uses, inside a closed Prop-valued definition with the suffix Statement,
preserving binder order, binder kinds and the source's universe-zero field
types; the two named instance binders become anonymous. Write published
names in full instead of using the source namespace openings, and replace
the source imports by the published modules defining the objects named in
the statement. Defer the truth proof; install no instance or simp
registration. Omit all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.IsSepClosed
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Relative.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions

/-!
# Relative norms on actual fixed fields: statement

A closed proposition saying that the class-formation relative norm on fixed
units of the separably closed ambient field is the ordinary field norm
between the two concrete fixed fields, without a normality assumption on the
intermediate extension.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The class-formation relative norm on fixed coefficients is the ordinary
field norm between the two concrete fixed fields, without a normality
assumption on the intermediate extension. -/
def relativeNorm_abstractFixedFieldUnit_eq_normUnitsStatement : Prop :=
  ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite
      (K.toSubgroup ⧸
        Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK)]
    [Finite
      ((Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)).toSubgroup ⧸
        Langlands.NYLL.CyclicCohomology.extensionSubgroup
          (Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)) K
          (Langlands.NYLL.ClassFormation.le_baseField K))]
    (x : (abstractRelativeFixedField k Ω hLK)ˣ),
    Langlands.NYLL.ClassFormation.relativeNorm
        (galoisAmbientUnitsRep k Ω) K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) =
      abstractFixedFieldUnitsEquivGaloisFixed k Ω K
        (Additive.ofMul
          (Langlands.NYLL.LocalFieldTheory.normUnits
            (abstractFixedField k Ω K)
            (abstractRelativeFixedField k Ω hLK) x))

end Langlands.NYLL.LocalClassFieldTheory
