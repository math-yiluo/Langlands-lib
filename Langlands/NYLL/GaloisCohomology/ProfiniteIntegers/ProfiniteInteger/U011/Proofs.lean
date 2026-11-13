/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U014.Proofs

/-!
# Index of natural multiplication on the NYLL profinite integers

Modified by Worker 241: extract M009.011 from the pinned NYLL source, prefix
the namespace with Langlands.NYLL, state the theorem using its published
Statement definition. Integrated by Integrator using the existing M009U014
index theorem in place of the duplicated proof calculation.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- The additive index of `n ℤ̂` in `ℤ̂` is `n`. -/
theorem zHatMulNat_range_index (n : ℕ) (hn : 0 < n) :
    zHatMulNat_range_indexStatement n hn :=
  Langlands.NYLL.PortInternal.M009U014.zHatMulNat_range_index n hn

end
end Langlands.NYLL.ClassFormation
