/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 165, 13 November 2026 UTC:
Extract only the proof of M024.002 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published Norm Statements module.
State the theorem as the published Statement applied to the source
parameters; the original proof rfl is retained unchanged. The source
simp attribute is not retained. Omit the source noncomputable section,
open CyclicCohomology and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Statements

/-!
# Relative coset action on a representative

The exact proof that the relative coset action of a fixed coefficient at the
coset of `k` is the action of `k` itself.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The relative coset action on a quotient representative is the corresponding group action. -/
theorem relativeCosetAction_mk
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) :
    relativeCosetAction_mkStatement A K L hLK a k :=
  rfl

end Langlands.NYLL.ClassFormation
