/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 169: extracted the M164.003 proof into a focused module,
added the Langlands.NYLL namespace prefix, stated the result using its published
Prop target, reused the published M164.001 instance locally, and imported the
separately published M164.002 proof. The source proof route is unchanged.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct.U002.Proofs

/-!
# The norm as a product of embeddings into a separably closed field

Adapted by Worker 169 from NYLL M164.003, source commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean`,
lines 69–92. This proves the unchanged published statement using the separately
published M164.002 tower-product proof. See the paired Markdown.
-/

noncomputable section

open scoped BigOperators

namespace Langlands.NYLL.LocalClassFieldTheory

attribute [local instance] Langlands.NYLL.PortInternal.M164.d001

/-- Mapping the norm into a separably closed field gives the product of all
base-field embeddings. -/
theorem algebraMap_norm_eq_prod_embeddings_of_isSepClosed
    (k Ω E : Type) [Field k] [Field Ω] [Field E]
    [Algebra k Ω] [IsSepClosed Ω] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (x : E) :
    algebraMap_norm_eq_prod_embeddings_of_isSepClosedStatement k Ω E x := by
  unfold algebraMap_norm_eq_prod_embeddings_of_isSepClosedStatement
  have hx := Algebra.IsSeparable.isIntegral k x
  let : Algebra.IsSeparable k
      (IntermediateField.adjoin k ({x} : Set E)) :=
    Algebra.isSeparable_tower_bot_of_isSeparable k
      (IntermediateField.adjoin k ({x} : Set E)) E
  rw [Algebra.norm_eq_norm_adjoin k x, map_pow,
    ← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.norm_eq_prod_embeddings_gen Ω
      (IntermediateField.adjoin.powerBasis hx)
      (IsSepClosed.splits_codomain _
        (Algebra.IsSeparable.isSeparable k
          (IntermediateField.adjoin.powerBasis hx).gen))]
  · simpa only [IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.AdjoinSimple.algebraMap_gen] using
      (prod_embeddings_algebraMap_powerBasisGen_eq
        (L := IntermediateField.adjoin k ({x} : Set E)) (E := E)
        k Ω (IntermediateField.adjoin.powerBasis hx)).symm
  · exact Algebra.IsSeparable.isSeparable k _

end Langlands.NYLL.LocalClassFieldTheory
