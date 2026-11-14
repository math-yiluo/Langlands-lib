/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 331, 2026-11-14: extract M353.003, rename the source-private definition to
Langlands.NYLL.PortInternal.M353.d003, and replace the source imports by
focused Mathlib imports. Preserve the body and effective source parameters.
See the paired Markdown. Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finset.Dedup

/-! # Fixed-degree monomial enumeration -/

noncomputable section

universe w

namespace Langlands.NYLL.PortInternal.M353

variable {sigma : Type w} [Fintype sigma]

/-- The finite list of all monomials of a fixed total degree. -/
noncomputable def d003 (m : ℕ) :
    List {d : sigma →₀ ℕ // d.degree = m} :=
  letI : Fintype {d : sigma →₀ ℕ // d.degree = m} :=
    (Finsupp.finite_of_degree_eq m).fintype
  Finset.univ.toList

end Langlands.NYLL.PortInternal.M353

end
