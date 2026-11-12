/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 126: extracted the M164.002 proof, added the Langlands.NYLL
namespace prefix, and made its type the published Prop-valued statement.
The published local instance M164.001 is re-enabled without redefining it.
The source proof route is retained. The sole import is the published statement
module. Retained attribution: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct.Statements

/-!
# Product of embeddings in a finite separable tower

Proof of NYLL M164.002 from `SeparableNormProduct.lean`, lines 37–65, at
commit fbd320cd8b1b06487c58227e92eb135794267709.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.NYLL.LocalClassFieldTheory

attribute [local instance] Langlands.NYLL.PortInternal.M164.d001

/-- The product over embeddings of the upper field restricts to the product
over embeddings of the lower field raised to the relative degree. -/
theorem prod_embeddings_algebraMap_powerBasisGen_eq
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
    {L E : Type} [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [Algebra.IsSeparable k E] [FiniteDimensional k E]
    (pb : PowerBasis k L) :
    prod_embeddings_algebraMap_powerBasisGen_eqStatement (E := E) k Ω pb := by
  unfold prod_embeddings_algebraMap_powerBasisGen_eqStatement
  have : FiniteDimensional L E := FiniteDimensional.right k L E
  have : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable k L E
  let : Fintype (L →ₐ[k] Ω) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.prod_equiv algHomEquivSigma
    (fun σ : E →ₐ[k] Ω => σ (algebraMap L E pb.gen))
    (fun σ => σ.1 pb.gen)]
  · rw [← Finset.univ_sigma_univ, Finset.prod_sigma, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun σ _ => ?_
    let : Algebra L Ω := σ.toRingHom.toAlgebra
    simp_rw [Finset.prod_const]
    congr
    rw [Finset.card_univ, Fintype.card_eq_nat_card]
    exact AlgHom.natCard_of_splits L E Ω (fun x =>
      IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable L x))
  · intro σ
    change σ (algebraMap L E pb.gen) =
      (σ.comp (IsScalarTower.toAlgHom k L E)) pb.gen
    exact (AlgHom.comp_apply σ (IsScalarTower.toAlgHom k L E) pb.gen).symm

end Langlands.NYLL.LocalClassFieldTheory
