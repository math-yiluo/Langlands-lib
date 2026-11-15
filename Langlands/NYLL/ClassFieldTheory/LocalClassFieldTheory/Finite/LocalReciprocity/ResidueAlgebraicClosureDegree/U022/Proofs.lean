/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.U006.Proofs

/-!
# Finite local reciprocity: finite coordinates of the intrinsic residue degree (proof)

Modified by Worker 46: prove the published target
`Langlands.NYLL.LocalClassFieldTheory.finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement`
(M236.022) under the source theorem name in the `Langlands.NYLL` namespace,
under the source's `variable` blocks. The source proof is kept: it applies the
published proof of M168.006 (`restrictNormalHom_residueAbsoluteFrobenius`),
whose `Statement` type Lean unfolds when rewriting. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- Finite-coordinate compatibility for the intrinsic residue degree
(M236.022). -/
theorem finiteResidueFrobeniusExponentEquiv_symm_restrict_in
    (sigma : Omega ≃ₐ[k] Omega)
    (E : FiniteGaloisIntermediateField k Omega) :
    finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement k Omega sigma E := by
  have : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  have : IsGalois k Omega := {}
  let : Finite E := Module.finite_of_finite k
  show (finiteResidueFrobeniusExponentEquiv k E).symm
        (AlgEquiv.restrictNormalHom E sigma) =
      Multiplicative.ofAdd
        (zHatReduction (Module.finrank k E) Module.finrank_pos
          (residueAbsoluteDegreeIn k Omega sigma).toAdd)
  apply (finiteResidueFrobeniusExponentEquiv k E).injective
  rw [(finiteResidueFrobeniusExponentEquiv k E).apply_symm_apply]
  change AlgEquiv.restrictNormalHom E sigma =
    finiteResidueFrobeniusIntermediate k Omega E
      (residueAbsoluteDegreeIn k Omega sigma)
  rw [← restrictNormalHom_residueAbsoluteFrobenius]
  congr 1
  exact ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply sigma).symm

end
end Langlands.NYLL.LocalClassFieldTheory
