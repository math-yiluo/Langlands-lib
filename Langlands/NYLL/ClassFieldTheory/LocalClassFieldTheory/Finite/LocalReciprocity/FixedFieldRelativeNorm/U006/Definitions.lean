/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only M276.006 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldRelativeNorm.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix and keep the source section
variables, docstring, signature and body. The body cites the private source
theorems abstractFixedFieldCosetToAlgHom_injective and
abstractFixedFieldCosetToAlgHom_surjective by their published names
Langlands.NYLL.PortInternal.M276.d005 and d004, applied to the same
arguments. Replace the source imports by the two published proof modules,
and open only the namespace of extensionSubgroup. Omit all other
declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U005.Proofs

/-!
# Relative cosets are the embeddings of a finite fixed field

The bijection between the left cosets of the abstract fixing subgroup of an
upper fixed field and the embeddings of that field into the common
separably closed ambient field over a lower fixed field.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.CyclicCohomology

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]

/-- Abstract relative left cosets are precisely the embeddings of the upper
concrete fixed field into the ambient separably closed field. -/
def abstractFixedFieldCosetEquivAlgHom
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)] :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      (abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω) :=
  Equiv.ofBijective (abstractFixedFieldCosetToAlgHom k Ω K L hLK)
    ⟨Langlands.NYLL.PortInternal.M276.d005 k Ω K L hLK,
      Langlands.NYLL.PortInternal.M276.d004 k Ω K L hLK⟩

end Langlands.NYLL.LocalClassFieldTheory

end
