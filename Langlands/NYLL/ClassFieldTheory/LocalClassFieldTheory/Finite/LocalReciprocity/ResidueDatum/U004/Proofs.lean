/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueDatum.U003.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U011.Proofs

/-!
# Finite local reciprocity: the index of a finite degree image (proof)

Adapted from NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, lines 109–118 (M238.004),
with the section variables of lines 31–33. Worker 59 (draft) and Worker 737
prove the published target
`Langlands.NYLL.LocalClassFieldTheory.Internal.residueDatumIn_fieldImage_index_closedFixingSubgroupStatement`
under the source theorem name; they prefixed the namespaces by `Langlands.NYLL`,
supplied the source's private instances `IsAlgClosure k Omega` (M236.002) and
`IsGalois k Omega` (M236.003) by local `have`s, added a `show` that unfolds the
target, and replaced the NYLL imports by the published modules whose theorems
the proof uses. The source proof script is otherwise unchanged. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open Langlands.NYLL.RamificationTheory

open Langlands.NYLL.ClassFormation

noncomputable section

variable (k Omega : Type)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- Internal finite-coordinate calculation: the degree image of the fixing
subgroup has natural index equal to the ordinary residue-field degree.  Public
residue-degree APIs use `Cardinal` or a finite residue-field bundle. -/
theorem Internal.residueDatumIn_fieldImage_index_closedFixingSubgroup
    (E : FiniteGaloisIntermediateField k Omega) :
    Internal.residueDatumIn_fieldImage_index_closedFixingSubgroupStatement
      k Omega E := by
  have : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  have : IsGalois k Omega := {}
  show ((residueDatumIn k Omega).fieldImage
      (closedFixingSubgroup k Omega E)).index = Module.finrank k E
  rw [show (residueDatumIn k Omega).fieldImage
        (closedFixingSubgroup k Omega E) =
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range.toSubgroup from
      residueDatumIn_fieldImage_closedFixingSubgroup k Omega E,
    AddSubgroup.index_toSubgroup]
  exact zHatMulNat_range_index (Module.finrank k E) Module.finrank_pos

end
end Langlands.NYLL.LocalClassFieldTheory
