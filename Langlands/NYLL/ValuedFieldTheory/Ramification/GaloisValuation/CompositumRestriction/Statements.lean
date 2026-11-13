/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 314, 13 November 2026, from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709,
Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean
(M331.001–M331.003). Prefix the namespace with Langlands.NYLL; replace each
theorem and proof with a closed Prop-valued definition ending in Statement.
Retain all used source parameters, binder kinds, hypotheses and independent
universes; make the three implicit group universes explicit in the source text.
Replace the NYLL import and RamificationTheory opening with their published
Langlands.NYLL counterparts. Omit the redundant self-opening and the
noncomputable section. Disable unused-variable lint for named hypotheses.
Full source correspondence is in Statements.md.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.Galois.Basic
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Definitions

/-!
# Restriction from a compositum: proposition targets

The three source statements from CompositumRestriction.lean, with their original
generality. This module defines the targets and contains no proofs of them.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.RamificationTheory

set_option linter.unusedVariables false

universe u v w uG uG₁ uG₂

/-- Restriction to two normal intermediate fields is jointly injective when
the two fields generate the ambient field. -/
def restrictNormalHom_prod_injective_of_sup_eq_topStatement : Prop :=
  ∀ (K : Type u) {P : Type v} [Field K] [Field P] [Algebra K P]
    (E₁ E₂ : IntermediateField K P) [Normal K E₁] [Normal K E₂]
    (hsup : E₁ ⊔ E₂ = ⊤),
    Function.Injective
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := P) E₁).prod
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := P) E₂))

/-- If two normal intermediate fields generate a third intermediate field in
a common ambient extension, restriction from the generated field to the two
factors is jointly injective. -/
def intermediateFieldRestrictNormalHom_prod_injective_of_sup_eqStatement : Prop :=
  ∀ (K : Type u) [Field K] {Omega : Type w} [Field Omega] [Algebra K Omega]
    (E₁ E₂ F : IntermediateField K Omega)
    (hE₁ : E₁ ≤ F) (hE₂ : E₂ ≤ F)
    [Normal K E₁] [Normal K E₂]
    (hsup : E₁ ⊔ E₂ = F),
    Function.Injective
      ((intermediateFieldRestrictNormalHom E₁ F hE₁ :
          (F ≃ₐ[K] F) →* (E₁ ≃ₐ[K] E₁)).prod
        (intermediateFieldRestrictNormalHom E₂ F hE₂ :
          (F ≃ₐ[K] F) →* (E₂ ≃ₐ[K] E₂)))

/-- Two subgroups are equal when one jointly injective pair of homomorphisms
has equal right images and both left images are trivial. -/
def subgroup_eq_of_prod_map_injective_of_left_maps_eq_botStatement : Prop :=
  ∀ {G : Type uG} {G₁ : Type uG₁} {G₂ : Type uG₂}
    [Group G] [Group G₁] [Group G₂]
    (f₁ : G →* G₁) (f₂ : G →* G₂)
    (hinjective : Function.Injective (f₁.prod f₂))
    (A B : Subgroup G)
    (hA₁ : A.map f₁ = ⊥) (hB₁ : B.map f₁ = ⊥)
    (h₂ : A.map f₂ = B.map f₂),
    A = B

end Langlands.NYLL.LocalClassFieldTheory
