/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 172, 13 November 2026 UTC:
Extract the proof of M237.003, valuationSubringComapMap_isLocalHom, from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean
(lines 81-128) at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the
namespace by Langlands.NYLL. State the theorem as the published target
valuationSubringComapMap_isLocalHomStatement (F := F) A and unfold it first;
the tactic proof after that is the source proof unchanged. Import the
published Initial statement module instead of the source's imports.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
Submitted by Worker 106, 14 November 2026 UTC, from Worker 172's public
draft for Task 6030; the Lean code is unchanged from that draft.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicallyClosed.Initial.Statements

/-!
# Proof: the pulled-back valuation-ring map is local

Proof of the M237.003 target `valuationSubringComapMap_isLocalHomStatement`.
See the paired Markdown for the source map and the proof outline.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

section PurelyInseparableComap

variable {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]

/-- Pullback along a field embedding gives a local map of valuation rings. -/
theorem valuationSubringComapMap_isLocalHom (A : ValuationSubring Omega) :
    valuationSubringComapMap_isLocalHomStatement (F := F) A := by
  unfold valuationSubringComapMap_isLocalHomStatement
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have hx0 : (x : F) ≠ 0 := by
    intro hzero
    have hmapZero : valuationSubringComapMap (F := F) A x = 0 := by
      apply Subtype.ext
      simp [valuationSubringComapMap, hzero]
    exact Units.ne_zero u (hu.trans hmapZero)
  let xinv : A.comap (algebraMap F Omega) :=
    ⟨(x : F)⁻¹, by
      change algebraMap F Omega ((x : F)⁻¹) ∈ A
      rw [map_inv₀]
      have hu' : algebraMap F Omega (x : F) = ((u : A) : Omega) := by
        have h := congrArg Subtype.val hu
        exact h.symm
      rw [hu']
      have hinv : (((u : A) : Omega))⁻¹ = (((u⁻¹ : Aˣ) : A) : Omega) := by
        have hprod :
            ((u : A) : Omega) * (((u⁻¹ : Aˣ) : A) : Omega) = 1 := by
          have hprodA : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := u.val_inv
          exact congrArg A.subtype hprodA
        exact (eq_inv_of_mul_eq_one_right hprod).symm
      rw [hinv]
      exact (u⁻¹ : Aˣ).val.property⟩
  let xu : (A.comap (algebraMap F Omega))ˣ :=
    { val := x
      inv := xinv
      val_inv := by apply Subtype.ext; simp [xinv, hx0]
      inv_val := by apply Subtype.ext; simp [xinv, hx0] }
  exact ⟨xu, rfl⟩

end PurelyInseparableComap

end
end Langlands.NYLL.LocalClassFieldTheory
