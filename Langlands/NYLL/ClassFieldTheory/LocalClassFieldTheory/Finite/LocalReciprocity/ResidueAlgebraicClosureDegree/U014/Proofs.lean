/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Frobenius.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.U015.Proofs

/-!
# Finite local reciprocity: the Frobenius image is the whole Galois group (proof)

Modified by Worker 484: prove the published target
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobeniusRangeIn_eq_topStatement`
(M236.014) under the source theorem name in the `Langlands.NYLL` namespace,
under the source's `variable` blocks. The source proof combines M236.013 with
the infinite Galois correspondence. This proof instead derives the result from
the published M236.015 theorem `residueAbsoluteFrobenius_isAlgClosure_surjective`
(whose published proof establishes M236.013 and M236.014 locally): the image of
a surjective homomorphism is the whole group. No instance is declared. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- The intrinsic Frobenius image is the whole residue absolute Galois group
(M236.014). -/
theorem residueAbsoluteFrobeniusRangeIn_eq_top :
    residueAbsoluteFrobeniusRangeIn_eq_topStatement k Omega := by
  -- M236.015: the Frobenius homomorphism is surjective.
  have hsurj := residueAbsoluteFrobenius_isAlgClosure_surjective k Omega
  unfold residueAbsoluteFrobenius_isAlgClosure_surjectiveStatement at hsurj
  unfold residueAbsoluteFrobeniusRangeIn_eq_topStatement
  -- Every automorphism is the Frobenius image of some profinite integer.
  rw [eq_top_iff]
  intro sigma _
  exact hsurj sigma

end
end Langlands.NYLL.LocalClassFieldTheory
