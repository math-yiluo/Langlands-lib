/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Representation.Definitions

/-!
# Compatibility of the two fixed-unit carrier equivalences

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory ClassFormation
noncomputable section
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
omit [IsGalois k Ω] in
def abstractRelativeUnitsEquiv_extensionUnitsEquivStatement
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (x : (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).V) : Prop :=
abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
        (abstractExtensionFixedRepresentationUnitsEquiv
          k Ω K L hLK hnormal x) =
      extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep k Ω) K L hLK hnormal x

end
end Langlands.NYLL.LocalClassFieldTheory
