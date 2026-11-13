/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Quotient.Definitions

/-!
# Kernel and surjectivity of the relative quotient homomorphism

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory
noncomputable section
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
def abstractRelativeToAmbientQuotient_kerStatement
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) : Prop :=
    letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
      abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal).ker =
      L.toSubgroup.subgroupOf K.toSubgroup

def abstractRelativeToAmbientQuotient_surjectiveStatement
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) : Prop :=
    letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
      abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    Function.Surjective
      (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal)

end
end Langlands.NYLL.LocalClassFieldTheory
