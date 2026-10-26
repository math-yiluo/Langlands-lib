/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 449 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
prove the published universal statement in Langlands.NYLL directly from
Mathlib's integer ring, finite quotient and adic separatedness interfaces.
No NYLL complete discrete valuation field construction is imported.
The original license and notice are retained in licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SmallStatement
import Mathlib.Basic.Countable.Small
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Universe-zero smallness of nonarchimedean local fields

The integer ring injects into its sequence of finite quotients by powers of
its maximal ideal. The field is a surjective image of pairs of integers.
-/

namespace Langlands.NYLL.LocalFieldTheory

open ValuativeRel

universe u

/-- Every nonarchimedean local field, in any carrier universe, is small in
universe zero. This proves the complete published universal statement. -/
theorem nonarchimedeanLocalField_small :
    nonarchimedeanLocalField_smallStatement.{u} := by
  intro K _ _ _ _
  let O := 𝒪[K]
  let I : Ideal O := 𝓂[K]
  have : Finite (O ⧸ I) := inferInstanceAs (Finite 𝓀[K])
  have (n : ℕ) : Finite (O ⧸ I ^ n) :=
    Ideal.finite_quotient_pow (Ideal.fg_of_isNoetherianRing I) n
  have hO : Small.{0} O := by
    let f : O → (∀ n : ℕ, O ⧸ I ^ n) :=
      fun x n => Ideal.Quotient.mk (I ^ n) x
    have hf : Function.Injective f := by
      intro x y h
      apply (IsHausdorff.eq_iff_smodEq (I := I)).2
      intro n
      simpa [f, Ideal.Quotient.mk_eq_mk_iff_sub_mem, SModEq] using congrFun h n
    exact small_of_injective hf
  have : Small.{0} O := hO
  apply small_of_surjective
    (f := fun p : O × O => (algebraMap O K p.1) / (algebraMap O K p.2))
  intro x
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective O x
  exact ⟨(a, b), hab⟩

end Langlands.NYLL.LocalFieldTheory
