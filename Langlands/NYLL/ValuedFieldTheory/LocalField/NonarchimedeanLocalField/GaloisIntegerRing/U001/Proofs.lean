/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 135, 14 November 2026:
Extract the proof of M139.001 (lines 34–51) from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and prove the published closed statement by introducing its
telescope before the unchanged source tactic proof. Import only the target
statement module. Omit all other source declarations. See paired Markdown.
The upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.PreservationStatement

/-!
# Galois automorphisms preserve an integral-closure valuation ring

The exact proof of NYLL M139.001.
-/

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel

/-- A Galois automorphism preserves the valuation integer ring when that ring is the
integral closure of the base valuation integer ring. -/
theorem galoisGroup_mem_integerRing_of_isIntegralClosure.{u} :
    galoisGroup_mem_integerRing_of_isIntegralClosureStatement.{u} := by
  intro K L _ _ _ _ _ _ _ σ x
  have hx : IsIntegral 𝒪[K] ((x : 𝒪[L]) : L) :=
    (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2
      ⟨x, rfl⟩
  have hσ : IsIntegral 𝒪[K] (σ ((x : 𝒪[L]) : L)) :=
    IsIntegral.map σ.toAlgHom hx
  rcases (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).1 hσ
    with ⟨y, hy⟩
  exact hy ▸ y.2

end Langlands.NYLL.LocalFieldTheory
