/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 320, 2026-11-16: extract M354.013 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, and use the exact published proposition as the theorem type.
Use focused imports, explicitly expose that proposition before the source
proof, and omit unrelated declarations and unused section settings.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U013.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst

/-!
# The zero intertwiner

Proof of the exact published M354.013 target by substitution at zero and
preservation of zero by the substitution algebra homomorphism.
-/

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- Zero intertwines any two Lubin--Tate series with the same prescribed
coefficient (NYLL M354.013). -/
theorem intertwines_zero
    [Finite σ]
    (e ebar : LubinTateSeries F π) :
    intertwines_zeroStatement (σ := σ) e ebar := by
  change Intertwines e ebar (0 : MvPowerSeries σ F.valuationSubring)
  rw [Intertwines]
  change
    MvPowerSeries.subst
        (0 : Unit →
          MvPowerSeries σ F.valuationSubring)
        e.toPowerSeries =
      MvPowerSeries.subst
        (fun i : σ => inVariable ebar i) 0
  rw [MvPowerSeries.subst_zero_of_constantCoeff_zero
    e.constantCoeff_eq_zero]
  rw [← MvPowerSeries.substAlgHom_apply
    (inVariable_hasSubst ebar), map_zero]

end SameUniformizer
end Langlands.NYLL.LubinTate
