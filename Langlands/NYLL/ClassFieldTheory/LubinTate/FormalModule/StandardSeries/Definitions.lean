/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 410, 2026-11-14: extract only M338.002 (lines 42–58)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL; replace the original
CoefficientEquation import by the focused published modules for the
polynomial series, the LubinTateSeries package and LocalField, and the
Mathlib module of Finite.one_lt_card; in the proof of the field
map_residue_eq_frobenius, replace the not yet proved
SameUniformizer.residueMap_uniformizer_eq_zero hπ by a local proof of the
same fact from Mathlib's IsLocalRing.residue_eq_zero_iff,
Valuation.mem_maximalIdeal_iff and Valuation.IsUniformizer.val_lt_one;
and replace the module documentation. The definition's name, parameters,
type, underlying series and the other two field proofs are unchanged.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardSeries.PolynomialSeries
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The standard Lubin--Tate series

For a uniformizer `π`, the polynomial power series `π X + X ^ q`, where `q`
is the cardinality of the residue field, is packaged as a Lubin--Tate
series. No equal-characteristic assumption is made.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- A uniformizer makes `π X + X ^ q` into a Lubin--Tate series. -/
noncomputable def standardLubinTateSeries
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) :
    LubinTateSeries F π where
  toPowerSeries := standardLubinTatePowerSeries F π
  constantCoeff_eq_zero := by
    have hq0 : Nat.card F.residueField ≠ 0 :=
      Nat.ne_of_gt (lt_trans Nat.zero_lt_one
        (Finite.one_lt_card (α := F.residueField)))
    simp [standardLubinTatePowerSeries, hq0]
  coeff_one_eq_uniformizer := by
    have hq : 1 ≠ Nat.card F.residueField :=
      (Finite.one_lt_card (α := F.residueField)).ne
    simp [standardLubinTatePowerSeries, PowerSeries.coeff_X_pow, hq]
  map_residue_eq_frobenius := by
    have hres : F.residueMap π = 0 :=
      (IsLocalRing.residue_eq_zero_iff π).2
        ((Valuation.mem_maximalIdeal_iff (v := F.toCompleteDVF.valuation)).2
          hπ.val_lt_one)
    simp [standardLubinTatePowerSeries, hres]

end Langlands.NYLL.LubinTate

end
