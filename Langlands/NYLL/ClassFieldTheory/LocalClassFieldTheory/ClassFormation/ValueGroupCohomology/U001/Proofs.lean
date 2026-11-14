/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 120, 14 November 2026: extract the proof of M141.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ValueGroupCohomology.lean,
lines 33-46, at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix
the namespace with Langlands.NYLL, import only the published
ValueGroupCohomology Statements module, and prove the published target
applied to all its parameters, after unfolding it. Since no proof of
galoisGroupValueGroupMulDistribMulAction_smul (M140.006) is in the Library,
it is proved as a local fact by its original rfl and used in place of that
source lemma in the original simp only call. Omit the source noncomputable
section and all other source declarations. See the paired Markdown; the
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.Statements

/-!
# The norm on the trivial value-group module

For the trivial Galois action on `Multiplicative ℤ`, the finite-group norm is
multiplication by the order of the Galois group.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.CyclicCohomology
open Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe u

/-- On the trivially acted-on value group, the finite-group norm is
multiplication by the order of the Galois group. -/
theorem galoisGroupValueGroup_tateNorm_toAdd
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (a : Multiplicative Int) :
    galoisGroupValueGroup_tateNorm_toAddStatement K L a := by
  unfold galoisGroupValueGroup_tateNorm_toAddStatement
  let := galoisGroupValueGroupMulDistribMulAction K L
  -- The source theorem M140.006, proved by its original `rfl`.
  have hsmul : ∀ (σ : Gal(L / K)) (n : Multiplicative Int), σ • n = n := by
    intro σ n
    rfl
  have hnorm : tateNorm (Gal(L / K)) (Multiplicative Int) a =
      a ^ Fintype.card (Gal(L / K)) := by
    simp only [tateNorm, hsmul, Finset.prod_const, Finset.card_univ]
  simpa only [toAdd_pow, nsmul_eq_mul] using
    congrArg Multiplicative.toAdd hnorm

end Langlands.NYLL.LocalClassFieldTheory
