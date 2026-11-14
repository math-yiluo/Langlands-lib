/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M101.006
(abstractRelativeUnitsEquiv_extensionUnitsEquiv) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published AbstractFixedFieldUnits
Representation Statements module. Merge the source namespace openings into
one line, omit the unused `open LocalFieldTheory` and `open CategoryTheory`,
keep the noncomputable section, the section variable line, `omit
[IsGalois k Ω] in`, the docstring and the `@[simp]` attribute. Write the
normality binder with the Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup`
of the source abbreviation `extensionSubgroup K L hLK`, as the published
statement does, and state the theorem as the published Statement applied to
the source parameters. The proof is unchanged. The original LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Representation.Statements

/-!
# Compatibility of the two fixed-unit carrier equivalences

The proof that the carrier comparison of the descended extension
representation with the units of the upper fixed field, followed by the
identification of those units with fixed coefficients, is the fixed-carrier
equivalence of the extension representation.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory ClassFormation
noncomputable section
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

omit [IsGalois k Ω] in
/-- States the theorem `abstractRelativeUnitsEquiv_extensionUnitsEquiv`. -/
@[simp]
theorem abstractRelativeUnitsEquiv_extensionUnitsEquiv
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (x : (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).V) :
    abstractRelativeUnitsEquiv_extensionUnitsEquivStatement k Ω K L hLK hnormal x := by
  exact (abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK).apply_symm_apply
      (extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep k Ω) K L hLK hnormal x)

end
end Langlands.NYLL.LocalClassFieldTheory
