/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 14 November 2026:
Extract only M277.005 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldNormResidueNaturality.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and keep the source section variables, docstring, binders and body.
Replace the source imports by the published modules defining the
quotient/Galois equivalence and the abelianized restriction, and open only
the namespaces of extensionSubgroup and
normResidueNaturalityAbelianizedRestriction. Omit all other declarations of
the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U019.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Equivalences.Definitions

/-!
# Abelianized restriction between concrete relative Galois groups

Restriction in a square of concrete fixed fields, between the abelianized
Galois groups of the two relative extensions, obtained by transporting the
class-formation abelianized restriction through the canonical
quotient/Galois equivalences.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.CyclicCohomology Langlands.NYLL.ClassFormation

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Restriction between the abelianized actual relative Galois groups in a
fixed-field square, transported through the canonical quotient/Galois
equivalences. -/
noncomputable def abstractFixedFieldAbelianizedRestriction
    (K K' L L' : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hL'K' /
          abstractFixedField k Ω K')) →+
      Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K)) :=
  MonoidHom.toAdditive
    ((abstractExtensionQuotientEquivGaloisGroup
      k Ω K L hLK hLnormal).abelianizationCongr.toMonoidHom.comp
      ((normResidueNaturalityAbelianizedRestriction K K' L L'
        hLK hL'K' hK'K hL'L).comp
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K' L' hL'K'
          hL'normal).abelianizationCongr.symm.toMonoidHom))

end Langlands.NYLL.LocalClassFieldTheory

end
