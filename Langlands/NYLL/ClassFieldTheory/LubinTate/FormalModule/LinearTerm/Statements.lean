/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Targets for prescribed linear terms

Modified by Worker 343: extract the signatures of M347.002, M347.004 and
M347.005 from the pinned NYLL LinearTerm.lean, prefix their namespaces with
Langlands.NYLL, and replace the theorems by Prop-valued Statement definitions.
Reuse the published linearForm and HasLinearTerm definitions. Preserve the
independent coefficient and variable universes and all source hypotheses;
underscore unused hypothesis names. The source simp attribute belongs to the
later proof of constantCoeff_linearForm. See the paired Markdown and
licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.LubinTate.SameUniformizer

universe u v

variable {R : Type u} [CommRing R]
variable {σ : Type v} [Fintype σ]

/-- Target: a multivariable linear form has zero constant coefficient. -/
def constantCoeff_linearFormStatement (L : σ → R) : Prop :=
  MvPowerSeries.constantCoeff (linearForm L) = 0

namespace HasLinearTerm

variable {H : MvPowerSeries σ R} {L : σ → R}

/-- Target: a series with prescribed linear term has zero constant coefficient. -/
def constantCoeff_eq_zeroStatement (_h : HasLinearTerm H L) : Prop :=
  MvPowerSeries.constantCoeff H = 0

/-- Target: a series with prescribed linear term admits univariate substitution. -/
def hasSubstStatement (_h : HasLinearTerm H L) : Prop :=
  PowerSeries.HasSubst H

end HasLinearTerm

end Langlands.NYLL.LubinTate.SameUniformizer
