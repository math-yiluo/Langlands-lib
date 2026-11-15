/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 126, 2026-11-15: extract only the source theorem M349.001
(`mvPowerSeries_expand_natCard`, source lines 32-55) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL; state it as a proof of the published target
`mvPowerSeries_expand_natCardStatement`; add a leading `show _ = _` to the
source proof; keep only the imports the proof needs; omit the other source
declarations, the source `open` and the source `noncomputable section`;
replace the module documentation. The original LICENSE and NOTICE remain in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.ExpandNatCardStatement
import Mathlib.FieldTheory.Finite.Basic

/-!
# Multivariable finite-field Frobenius expansion

Proof of the target `mvPowerSeries_expand_natCardStatement` (M349.001): over a
finite field `k`, replacing each variable of a multivariable power series by
its `Nat.card k`-th power gives the `Nat.card k`-th power of the series.
-/

universe u w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

/-- Multivariable finite-field Frobenius (M349.001): replacing each variable by
its `q`th power, where `q = Nat.card k`, is the same as taking the `q`th power
of the whole series. -/
theorem mvPowerSeries_expand_natCard
    {k : Type u} [Field k] [Finite k]
    {σ : Type w} [Finite σ] (f : MvPowerSeries σ k) :
    mvPowerSeries_expand_natCardStatement f := by
  show _ = _
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases FiniteField.card k p with ⟨⟨n, npos⟩, ⟨hpprime, hn⟩⟩
  let : Fact p.Prime := ⟨hpprime⟩
  have hncard : Fintype.card k = p ^ n := by
    simpa using hn
  have hn' : Nat.card k = p ^ n := by
    simpa only [Nat.card_eq_fintype_card] using hncard
  have hpow :
      MvPowerSeries.expand (p ^ n) (pow_ne_zero n hpprime.ne_zero) f =
        f ^ (p ^ n) := by
    rw [← MvPowerSeries.map_iterateFrobenius_expand,
      iterateFrobenius_eq_pow, FiniteField.frobenius_pow hncard,
      RingHom.one_def, MvPowerSeries.map_id]
    · rfl
    · exact hpprime.ne_zero
  simpa only [hn'] using hpow

end SameUniformizer
end Langlands.NYLL.LubinTate
