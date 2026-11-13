/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 165, 13 November 2026 UTC:
Extract only the proof of M024.004 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published Norm Statements module.
State the theorem as the published Statement applied to the source
parameters; the original proof rfl is retained unchanged. The source
simp attribute is not retained. Omit the source noncomputable section,
the unused section variables and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Statements

/-!
# Left multiplication on a coset representative

The exact proof that the left-multiplication permutation of `g` sends the
coset of `x` to the coset of `g * x`.
-/

namespace Langlands.NYLL.ClassFormation

/-- Left multiplication sends the coset of `x` to the coset of `g * x`. -/
theorem leftMulCosetEquiv_mk {G : Type*} [Group G]
    (H : Subgroup G) (g x : G) :
    leftMulCosetEquiv_mkStatement H g x :=
  rfl

end Langlands.NYLL.ClassFormation
