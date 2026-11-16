/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Extract the proof of M272.007
(localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldLocalData.lean at fbd320cd8b1b06487c58227e92eb135794267709 and
state it as a proof of the published closed proposition
localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement.
Add the Langlands.NYLL namespace prefix, also in the opened namespaces.
Introduce the quantified variables with intro. Import the published Library
modules that supply the M272.006 and M249.010 theorems, instead of the source
imports. Omit the noncomputable section, the open lines the proof does not
need, and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U010.Proofs

/-!
# The decomposition group of the chosen valuation ring over a finite
separable extension: proof

Proof of the published proposition
`localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement`
(source row M272.007).
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped Pointwise
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- After identifying separable closures over a finite separable local
extension, the ambient selected valuation ring is stabilized by the whole
absolute Galois group of the extension field. -/
theorem localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv :
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquivStatement := by
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
  let AF := localSeparableValuationSubring F
  have hAF :
      AF = A.comap e.toRingHom :=
    localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
      K F i e
  have hAFtop :
      decompositionGroup F AF = ⊤ :=
    localSeparableDecompositionGroup_eq_top F
  apply top_unique
  intro sigma _hsigma
  let sigmaF : Gal(SeparableClosure F / F) :=
    AlgEquiv.autCongr e.symm sigma
  have hsigmaF :
      sigmaF • AF = AF := by
    have :
        sigmaF ∈ decompositionGroup F AF := by
      rw [hAFtop]
      trivial
    change sigmaF • AF = AF at this
    exact this
  change sigma • A = A
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hmem (z : SeparableClosure K) :
      e.symm z ∈ AF ↔ z ∈ A := by
    rw [hAF]
    change e (e.symm z) ∈ A ↔ z ∈ A
    rw [e.apply_symm_apply]
  rw [← hmem (sigma⁻¹ • x), ← hmem x]
  have hx :=
    congrArg
      (fun B : ValuationSubring (SeparableClosure F) =>
        e.symm x ∈ B)
      hsigmaF
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simpa [sigmaF, AlgEquiv.autCongr_apply] using hx.to_iff

end Langlands.NYLL.LocalClassFieldTheory
