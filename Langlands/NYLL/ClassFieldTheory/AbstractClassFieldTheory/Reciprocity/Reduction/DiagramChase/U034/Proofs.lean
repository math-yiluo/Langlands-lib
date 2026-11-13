/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 60, 13 November 2026 UTC:
Extract only the proof of M077.034 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 751–768). Add the
Langlands.NYLL namespace prefix, import the published DiagramChase
Statements module and add the focused Mathlib import
Mathlib.GroupTheory.Abelianization.Defs, which supplies
Abelianization.commutator_subset_ker used by the original proof. State
the theorem as the published Statement applied to the source parameters,
and insert a `show` step exposing the equation `r (Additive.ofMul q) = 0`
before the original proof, which is otherwise unchanged. Omit the source imports, opens, noncomputable section, universe,
section variables and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.DiagramChase.Statements
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Additive homomorphisms into abelian groups kill commutators

The automatic inclusion in the kernel statement of the first reduction of the
abstract reciprocity theorem: an additive homomorphism from `Additive Q` into an
abelian group vanishes on every element of the commutator subgroup of `Q`.
-/

namespace Langlands.NYLL.ClassFormation

/-- Every additive homomorphism from a group into an abelian group kills
the commutator subgroup.  This is the automatic inclusion in the kernel
statement of the first reduction. -/
theorem abstractReciprocity_commutator_mem_kernel
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (r : Additive Q →+ B) (q : Q)
    (hq : q ∈ commutator Q) :
    abstractReciprocity_commutator_mem_kernelStatement r q hq := by
  show r (Additive.ofMul q) = 0
  let rMul : Q →* Multiplicative B :=
    { toFun := fun x => Multiplicative.ofAdd (r (Additive.ofMul x))
      map_one' := r.map_zero
      map_mul' := r.map_add }
  have hker : q ∈ rMul.ker :=
    Abelianization.commutator_subset_ker rMul hq
  change Multiplicative.ofAdd (r (Additive.ofMul q)) = 1 at hker
  exact Multiplicative.ofAdd.injective (by simpa using hker)

end Langlands.NYLL.ClassFormation
