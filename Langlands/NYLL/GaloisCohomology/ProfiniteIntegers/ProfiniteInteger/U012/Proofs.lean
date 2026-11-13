/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Statements
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U014.Proofs

/-!
# Finite-index additive subgroups of the NYLL profinite integers

Modified by Worker 242: isolate M009.012 from the pinned NYLL source, prefix
the namespace with Langlands.NYLL, and give the theorem its published Statement
as type. Integrator reuses the identical published M009U014 internal theorem.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Every additive subgroup of nonzero index is the image of multiplication
by its index. -/
theorem zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero
    (H : AddSubgroup ZHat) (hH : H.index ≠ 0) :
    zHatAddSubgroup_eq_mulNat_range_of_index_ne_zeroStatement H hH :=
  Langlands.NYLL.PortInternal.M009U014.zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero H hH

end
end Langlands.NYLL.ClassFormation
