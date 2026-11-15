/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 123 and Worker 721 (2026-11): extract the M168.006
proof (source lines 115-124) from the pinned source at
fbd320cd8b1b06487c58227e92eb135794267709; prefix its namespace by
Langlands.NYLL, import its published Prop target, and state the theorem with
that exact target as its type. The proof script is unchanged. Retained license
and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.Absolute.Statements

/-!
# M168.006: restriction of the absolute Frobenius action (proof)
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
variable (k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [IsGalois k Omega]

/-- Restricting the assembled Frobenius to a finite Galois intermediate
field gives exactly the finite Frobenius coordinate. -/
theorem restrictNormalHom_residueAbsoluteFrobenius
    (z : ZHatMul) (E : FiniteGaloisIntermediateField k Omega) :
    restrictNormalHom_residueAbsoluteFrobeniusStatement k Omega z E := by
  have hcomponent := congrArg (fun q => q.val (op E))
    ((InfiniteGalois.continuousMulEquivToLimit k Omega).apply_symm_apply
      (residueFrobeniusToLimit k Omega z))
  exact hcomponent

end
end Langlands.NYLL.LocalClassFieldTheory
