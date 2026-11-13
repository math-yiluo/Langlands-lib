/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.Initial.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions

/-!
# Galois-fixed ambient unit targets

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory KummerTheory
noncomputable section
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
def intermediateFieldUnitsToGaloisAmbient_applyStatement
    (E : IntermediateField K Ω) (x : Eˣ) : Prop :=
intermediateFieldUnitsToGaloisAmbient K Ω E (Additive.ofMul x) =
      Additive.ofMul (Units.map E.val.toRingHom x)

variable [IsGalois K Ω]
def mem_galoisAmbientUnits_fixed_iffStatement
    (E : IntermediateField K Ω)
    (x : Additive Ωˣ) : Prop :=
x ∈ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω E) ↔
      ((Additive.toMul x : Ωˣ) : Ω) ∈ E

def intermediateFieldUnitsToGaloisAmbient_rangeStatement
    (E : IntermediateField K Ω) : Prop :=
(intermediateFieldUnitsToGaloisAmbient K Ω E).range =
      ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup K Ω E)

end
end Langlands.NYLL.LocalClassFieldTheory
