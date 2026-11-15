/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 722, 2026-11-15: extract only the proof of private source
unit M353.005 (`mem_degreeIndexList`) from commit
fbd320cd8b1b06487c58227e92eb135794267709, rename it
Langlands.NYLL.PortInternal.M353.d005, conclude with the published
d005Statement target, and replace the source imports by the published
Statements module. The simp call also unfolds d005Statement and names d003.
See the paired Markdown. Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DegreeIndexList.Statements

/-! # Membership in the fixed-degree monomial enumeration -/

noncomputable section

universe w

namespace Langlands.NYLL.PortInternal.M353

/-- Every exponent vector of total degree `m` appears in the
fixed-degree enumeration `d003 m`. -/
theorem d005 {sigma : Type w} [Fintype sigma]
    (m : ℕ) (d : {d : sigma →₀ ℕ // d.degree = m}) :
    d005Statement (sigma := sigma) m d := by
  classical
  simp [d005Statement, d003]

/-- Check the entire unapplied theorem against the exact published target. -/
example : ∀ {sigma : Type w} [Fintype sigma] (m : ℕ)
    (d : {d : sigma →₀ ℕ // d.degree = m}),
    d005Statement (sigma := sigma) m d :=
  @d005

end Langlands.NYLL.PortInternal.M353

end
