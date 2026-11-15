/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 15 November 2026, from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709,
lines 21–47, 65–71 and 104–108 (M163.001–M163.003, M163.005, M163.009).
Integrator consolidated the source private abbreviations G and A (M163.001,
M163.002) with the published intrinsicAbsoluteGalois and intrinsicAbsoluteUnits
(M091.001, M091.002), whose bodies are exactly the source bodies. The three
public definitions retain their docstrings, types and bodies, with G and A
replaced by these existing names in Langlands.NYLL.LocalClassFieldTheory.
The source imports are replaced by the published dependencies below and
Mathlib's separable-closure module. The source opens are retained. All other
source declarations are omitted. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.IsSepClosed
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.BaseUnits.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions

/-!
# Finite local reciprocity: the base value group in `ℤ̂`

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/HenselianValuationBase.lean`,
lines 21–33 (namespace, opens, section variables), 35 and 37–38 (inventory
M163.001, M163.002), 40–47 (M163.003), 65–71 (M163.005) and 104–108
(M163.009).

The units `Kˣ` of a nonarchimedean local field are identified with the
coefficients fixed by the base subgroup of the absolute separable Galois group
(M163.003), which with its unit representation is the published intrinsic
absolute data (M091.001, M091.002). NYLL's valuation map on `Kˣ`, embedded in
the profinite integers `ℤ̂`, is transported to that fixed coefficient group
(M163.005), and its value
group is reduced modulo `n` (M163.009).
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory KummerTheory

open LocalFieldTheory

open ClassFormation

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- `Kˣ` is the coefficient group fixed by the distinguished base subgroup
of the absolute separable Galois group. -/
def baseFieldUnitsEquiv :
    Additive Kˣ ≃+ ambientFixedAddSubgroup (intrinsicAbsoluteUnits K) (baseField (intrinsicAbsoluteGalois K)) :=
  (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).trans
    (AddEquiv.addSubgroupCongr
      (congrArg (ambientFixedAddSubgroup (intrinsicAbsoluteUnits K))
        (closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K))))

/-- The normalized valuation `v_K : Kˣ → ℤ`, embedded in `ℤ̂` and written on
the actual fixed coefficient group. -/
def localBaseValuation :
    ambientFixedAddSubgroup (intrinsicAbsoluteUnits K) (baseField (intrinsicAbsoluteGalois K)) →+ ZHat :=
  (Int.castRingHom ZHat).toAddMonoidHom.comp
    ((LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K).comp
      (baseFieldUnitsEquiv K).symm.toAddMonoidHom)

/-- Reduction modulo `n` on the actual value group. -/
def localValueGroupReduction (n : ℕ) (hn : 0 < n) :
    (localBaseValuation K).range →+ ZMod n :=
  (zHatReduction n hn).toAddMonoidHom.comp
    (localBaseValuation K).range.subtype

end
end Langlands.NYLL.LocalClassFieldTheory
