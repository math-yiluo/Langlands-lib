/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the proof of the private theorem M086.018
normResidueNaturality_symm_naturality from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean at
fbd320cd8b1b06487c58227e92eb135794267709, as the theorem
Langlands.NYLL.PortInternal.M086.d018 proving the published d018Statement.
Introduce the statement's binders, naming the hypothesis h as in the
source, and keep the source tactic proof unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U018.Statements

/-!
# Inverting the horizontal isomorphisms of a commutative square: proof
-/

namespace Langlands.NYLL.PortInternal.M086

/-- A commutative square of additive isomorphisms remains commutative after
replacing both horizontal isomorphisms by their inverses (source unit
M086.018). -/
theorem d018.{u₁, u₂, u₃, u₄} : d018Statement.{u₁, u₂, u₃, u₄} := by
  intro Q B Q' B' _ _ _ _ r r' q b h
  apply AddMonoidHom.ext
  intro x
  apply r'.injective
  change r' (q (r.symm x)) = r' (r'.symm (b x))
  rw [r'.apply_symm_apply]
  have hx := DFunLike.congr_fun h (r.symm x)
  change b (r (r.symm x)) = r' (q (r.symm x)) at hx
  rw [r.apply_symm_apply] at hx
  exact hx.symm

end Langlands.NYLL.PortInternal.M086
