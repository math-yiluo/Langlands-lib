/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 344, 2026-11-13: extract only M336.001 and its three
simp attributes from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, replace the original LocalField
import by its focused published definition module, and focus the module
documentation. All four structure fields and their mathematical types are
unchanged. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.SetTheory.Cardinal.Finite
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Lubin--Tate power series with a prescribed linear coefficient

The chosen element is arbitrary in the valuation subring. The package records
the zero constant coefficient, its prescribed linear coefficient, and reduction
to the residue-field Frobenius power series.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- A Lubin--Tate series with prescribed linear coefficient π.

The first two fields specify the constant and linear terms. The final field
specifies coefficientwise reduction to the residue-field Frobenius series. -/
structure LubinTateSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) where
  /-- The underlying one-variable formal power series over `O_K`. -/
  toPowerSeries : PowerSeries F.valuationSubring
  /-- The constant coefficient of a Lubin--Tate series vanishes. -/
  constantCoeff_eq_zero :
    PowerSeries.constantCoeff toPowerSeries = 0
  /-- The linear coefficient is the chosen element `π`. -/
  coeff_one_eq_uniformizer :
    PowerSeries.coeff 1 toPowerSeries = π
  /-- Reduction to the residue field is the `q`-power Frobenius series. -/
  map_residue_eq_frobenius :
    PowerSeries.map F.residueMap toPowerSeries =
      (PowerSeries.X : PowerSeries F.residueField) ^
        Nat.card F.residueField

attribute [simp] LubinTateSeries.constantCoeff_eq_zero
  LubinTateSeries.coeff_one_eq_uniformizer
  LubinTateSeries.map_residue_eq_frobenius

end Langlands.NYLL.LubinTate

end
