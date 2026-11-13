/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract M266.006 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and replace the source imports by the focused published
prerequisites listed below. The definition and its telescope are unchanged.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U001.Definitions

/-!
# Multiplicative valuation modulo a degree

This module adapts M266.006, source lines 71–75 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

noncomputable section

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable def valuationModDegreeMulHom (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Kˣ →* Multiplicative (ZMod n) :=
  AddMonoidHom.toMultiplicativeRight (valuationModDegree K n)


end Langlands.NYLL.LocalClassFieldTheory
