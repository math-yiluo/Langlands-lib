/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Initial.Definitions

/-!
# Finite local reciprocity: finite subextensions of a residue algebraic closure (targets)

Modified by Worker 123: replace the source theorems M236.009 and M236.011 of the
pinned NYLL `ResidueAlgebraicClosureDegree` source by Prop-valued `Statement`
definitions in the `Langlands.NYLL` namespace, under the source's `variable`
blocks and `omit` commands so that every target keeps the source theorem's
complete parameter telescope and universes. The target of the source `@[simp]`
theorem M236.009 is reducible (`abbrev`) so that its later proof can carry the
attribute. Source proofs are omitted. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

omit [Algebra.IsAlgebraic k Omega] in
/-- Target of M236.009: the embedded degree-`n` finite Galois intermediate
field has degree `n` over `k`. -/
abbrev finrank_finiteResidueGaloisIntermediateFieldInStatement
    (n : ℕ) [NeZero n] : Prop :=
  Module.finrank k
      (finiteResidueGaloisIntermediateFieldIn k Omega n) = n

omit [IsAlgClosed Omega] in
/-- Target of M236.011: in any algebraic closure of a finite field, the fixed
points of arithmetic Frobenius are exactly the base field. -/
def mem_range_algebraMap_iff_frobenius_fixed_inStatement
    (x : Omega) : Prop :=
  x ∈ Set.range (algebraMap k Omega) ↔
    FiniteField.frobeniusAlgEquivOfAlgebraic k Omega x = x

end
end Langlands.NYLL.LocalClassFieldTheory
