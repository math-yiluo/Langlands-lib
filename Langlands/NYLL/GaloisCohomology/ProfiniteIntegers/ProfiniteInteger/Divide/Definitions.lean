/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U005.Proofs

/-!
# Division by a positive natural number on `n ℤ̂`

Modified by Worker 5264: extract M009.015 and M009.016 from the pinned NYLL
ProfiniteInteger source, prefix the namespace with Langlands.NYLL, and replace
the source imports by the published proof of M009.005 (`zHatMulNat_injective`),
which the body of M009.015 uses. The docstrings, signatures, construction
bodies and noncomputable section are retained.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Multiplication by `n > 0` identifies `ℤ̂` continuously with its image. -/
noncomputable def zHatMulNatRangeEquiv (n : ℕ) (hn : 0 < n) :
    ZHat ≃ₜ+ (zHatMulNat n).toAddMonoidHom.range := by
  let e : ZHat ≃+ (zHatMulNat n).toAddMonoidHom.range :=
    AddMonoidHom.ofInjective (zHatMulNat_injective hn)
  have he : Continuous e := by
    change Continuous fun x : ZHat =>
      (⟨zHatMulNat n x, ⟨x, rfl⟩⟩ : (zHatMulNat n).toAddMonoidHom.range)
    exact Continuous.subtype_mk (map_continuous (zHatMulNat n)) fun x => ⟨x, rfl⟩
  let h : ZHat ≃ₜ (zHatMulNat n).toAddMonoidHom.range :=
    he.homeoOfEquivCompactToT2
  exact
    { e with
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

/-- Division by `n` on the subgroup `n ℤ̂`. -/
noncomputable def zHatDivide (n : ℕ) (hn : 0 < n) :
    ContinuousAddMonoidHom ((zHatMulNat n).toAddMonoidHom.range) ZHat :=
  (zHatMulNatRangeEquiv n hn).symm

end
end Langlands.NYLL.ClassFormation
