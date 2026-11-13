/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Definitions

/-!
# Targets for division by a positive natural number on `n ℤ̂`

Modified by Worker 5264: extract the two public theorem signatures M009.017
and M009.018 from the pinned NYLL ProfiniteInteger source as Prop-valued
Statement definitions. Prefix the namespace with Langlands.NYLL, append
`Statement` to each name, keep every source parameter, binder kind and
hypothesis, and omit the proofs and `@[simp]` attributes.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Target for the identity `zHatMulNat n (zHatDivide n hn y) = y.1`. -/
def zHatMulNat_zHatDivideStatement (n : ℕ) (hn : 0 < n)
    (y : (zHatMulNat n).toAddMonoidHom.range) : Prop :=
  zHatMulNat n (zHatDivide n hn y) = y.1

/-- Target for the identity `zHatDivide n hn ⟨zHatMulNat n x, ⟨x, rfl⟩⟩ = x`. -/
def zHatDivide_zHatMulNatStatement (n : ℕ) (hn : 0 < n) (x : ZHat) : Prop :=
  zHatDivide n hn
    ⟨zHatMulNat n x, ⟨x, rfl⟩⟩ = x

end
end Langlands.NYLL.ClassFormation
