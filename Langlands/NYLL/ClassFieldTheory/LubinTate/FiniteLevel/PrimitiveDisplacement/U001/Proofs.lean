/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: isolate the M362.001 result from
commit fbd320cd8b1b06487c58227e92eb135794267709, rename the source-private
helper under Langlands.NYLL.PortInternal.M362, and prove its statement
target by specializing the published coefficient-restriction theorem.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement.U001.Statements
import Langlands.CommutativeAlgebra.MvPowerSeriesCoordinateChange
import Mathlib.Tactic.FinCases

universe u

namespace Langlands.NYLL.PortInternal.M362

theorem d001
    {R : Type u} [CommRing R]
    (f : MvPowerSeries (Fin 2) R) (d : Fin 2 →₀ ℕ)
    (hd : d 1 = 0) : d001Statement f d hd := by
  unfold d001Statement
  have hd' : Finsupp.single (0 : Fin 2) (d 0) = d := by
    ext i
    fin_cases i <;> simp [hd]
  have hfamily :
      Langlands.CommutativeAlgebra.MvPowerSeriesFactorial.restrictFamily
          (K := R) (n := 1) =
        ![(PowerSeries.X : PowerSeries R), 0] := by
    funext i
    fin_cases i <;> rfl
  simpa only [PowerSeries.coeff, hfamily, hd'] using
    (Langlands.CommutativeAlgebra.MvPowerSeriesFactorial.coeff_subst_restrictFamily
      (n := 1) f (d 0))

end Langlands.NYLL.PortInternal.M362
