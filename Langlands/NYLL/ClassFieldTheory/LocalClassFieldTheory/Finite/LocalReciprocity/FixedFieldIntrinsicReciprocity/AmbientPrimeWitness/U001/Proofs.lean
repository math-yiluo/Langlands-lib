/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the proof of M284.001 abelianizationCongr_symm_eq_primeTarget
from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeWitness.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published M284.001 Statements module. Prove its
closed proposition by introducing the ten binders, naming the anonymous
premise hprime, and then retaining the original congrArg, change and calc
proof. Omit the original noncomputable section, the unused namespace
openings and all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeWitness.U001.Statements

/-!
# Transport of an identified abelianized prime value: proof

The proof of the published closed assertion that moving an abelianized
value back through one quotient equivalence and forward through another
recovers the forward image of the abelianized ambient element that it was
identified with.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Transporting an identified abelianized prime value back through one
quotient equivalence and forward through another preserves its target. -/
theorem abelianizationCongr_symm_eq_primeTarget :
    abelianizationCongr_symm_eq_primeTargetStatement := by
  intro Q₀ G₀ G _ _ _ q₀ qE qAmbient r hprime
  have hprimeMul :=
    congrArg Additive.toMul hprime
  change
    Additive.toMul r =
      q₀.abelianizationCongr
        (Abelianization.of qAmbient) at hprimeMul
  calc
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul r)) =
        qE.abelianizationCongr
          (q₀.abelianizationCongr.symm
            (q₀.abelianizationCongr
              (Abelianization.of qAmbient))) :=
      congrArg qE.abelianizationCongr
        (congrArg q₀.abelianizationCongr.symm hprimeMul)
    _ = qE.abelianizationCongr
          (Abelianization.of qAmbient) := by
      rw [q₀.abelianizationCongr.symm_apply_apply]

end Langlands.NYLL.LocalClassFieldTheory
