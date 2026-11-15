/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Extract the proof of M272.006
(localSeparableValuationSubring_eq_comap_finiteExtensionEquiv) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldLocalData.lean at fbd320cd8b1b06487c58227e92eb135794267709 and
state it as a proof of the published closed proposition
localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement.
Add the Langlands.NYLL namespace prefix, also in the opened namespaces.
Introduce the quantified variables with intro. Import the published Library
modules that supply the statement and the results used, instead of the
source imports. Omit the noncomputable section, the open lines the proof
does not need, and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData.U006.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison.ComapEmbeddingProof
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U009.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U004.Proofs

/-!
# The chosen valuation rings under a finite separable extension: proof

Proof of the published proposition
`localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement`
(source row M272.006).
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

open Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation (
  hasExtension_valuation_of_valuationSubring_pullback
) in
/-- A separable-closure equivalence extending an embedding of a finite
separable local extension identifies the two uniquely extended local
valuation rings. -/
theorem localSeparableValuationSubring_eq_comap_finiteExtensionEquiv :
    localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement := by
  intro K F _ _ _ _ _ _ _ _ _ _ _ _ i
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F (SeparableClosure K)
  let : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  intro e
  let A := localSeparableValuationSubring K
  let B := A.comap e.toRingHom
  have hcomap :
      A.comap i.toRingHom =
        (ValuativeRel.valuation F).valuationSubring :=
    localSeparableValuationSubring_comap_embedding K F i
  have hBext :
      (localCompleteDVF F).valuation.HasExtension B.valuation := by
    apply
      hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change e (algebraMap F (SeparableClosure F) x) ∈ A ↔
      x ∈ (localCompleteDVF F).valuation.valuationSubring
    rw [e.commutes]
    change x ∈ A.comap i.toRingHom ↔
      x ∈ (ValuativeRel.valuation F).valuationSubring
    rw [hcomap]
  let : (localCompleteDVF F).valuation.HasExtension B.valuation :=
    hBext
  exact localSeparableValuationSubring_eq_of_hasExtension F B

end Langlands.NYLL.LocalClassFieldTheory
