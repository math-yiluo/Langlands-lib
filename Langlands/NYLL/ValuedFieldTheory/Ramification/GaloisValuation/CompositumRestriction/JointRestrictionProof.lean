/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 307, 14 November 2026, from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709,
Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean
(M331.001, statement lines 30–35 and proof lines 36–52).
Import the published proposition target and prove it under the adapted source
name in Langlands.NYLL. Introduce its closed quantifiers before retaining the
original kernel/fixing-subgroup proof. Omit the unrelated source declarations,
unused namespace openings and noncomputable section.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction.Statements

/-!
# Joint injectivity of restriction to two generating normal fields

The exact proof of the published M331.001 proposition.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

/-- Restriction to two normal intermediate fields is jointly injective when
the two fields generate the ambient field. -/
theorem restrictNormalHom_prod_injective_of_sup_eq_top :
    restrictNormalHom_prod_injective_of_sup_eq_topStatement.{u, v} := by
  intro K P _ _ _ E₁ E₂ _ _ hsup
  refine (injective_iff_map_eq_one _).mpr ?_
  intro sigma hsigma
  have hE₁ : AlgEquiv.restrictNormalHom (F := K) (K₁ := P) E₁ sigma = 1 :=
    congrArg Prod.fst hsigma
  have hE₂ : AlgEquiv.restrictNormalHom (F := K) (K₁ := P) E₂ sigma = 1 :=
    congrArg Prod.snd hsigma
  have hfixE₁ : sigma ∈ E₁.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact MonoidHom.mem_ker.mpr hE₁
  have hfixE₂ : sigma ∈ E₂.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact MonoidHom.mem_ker.mpr hE₂
  have hfix : sigma ∈ (E₁ ⊔ E₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hfixE₁, hfixE₂⟩
  rw [hsup, IntermediateField.fixingSubgroup_top] at hfix
  exact hfix

end Langlands.NYLL.LocalClassFieldTheory
