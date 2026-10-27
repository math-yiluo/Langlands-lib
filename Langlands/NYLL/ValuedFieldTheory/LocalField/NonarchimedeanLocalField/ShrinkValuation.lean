/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 231 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
the definition is placed in Langlands.NYLL with explicit binders, and the
private smallness wrapper is replaced by local use of the published theorem
nonarchimedeanLocalField_small in the type and the term-mode body. The NYLL
source import is replaced by the published smallness proof module, the
unused topology import is dropped, and Mathlib.Algebra.Ring.Shrink is
imported for Shrink.ringEquiv.
The original license and notice are retained in licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SmallProof
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Ring.Shrink

/-!
# The valuation on the universe-zero representative of a local field

A nonarchimedean local field `K` in any universe is small in universe zero.
This file pulls its canonical valuation back along `Shrink.ringEquiv K` to
the `Type 0` representative `Shrink.{0} K`, keeping the original value group.
-/

namespace Langlands.NYLL.LocalFieldTheory

open ValuativeRel

universe u

/-- The canonical valuation of `K`, pulled back to the universe-zero carrier
`Shrink.{0} K` along `Shrink.ringEquiv K : Shrink.{0} K ≃+* K`. Its values
lie in the original value group `ValueGroupWithZero K`. Smallness is supplied
locally by `nonarchimedeanLocalField_small`. -/
noncomputable def shrinkLocalFieldValuation (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    Valuation (Shrink.{0} K) (ValueGroupWithZero K) :=
  letI : Small.{0} K := nonarchimedeanLocalField_small K
  (valuation K).comap (Shrink.ringEquiv K).toRingHom

end Langlands.NYLL.LocalFieldTheory
