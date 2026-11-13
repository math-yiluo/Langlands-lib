/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 13 November 2026:
Extract the statement of M244.002 (toDecompositionGroupOfEqTop_coe) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
ResidueActionIndex.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued
definition without its proof. The section variables K, L and their field
and algebra binders become leading universal binders; the section variable
[IsGalois K L], which the source omits for this theorem, is not included.
Add the Langlands.NYLL namespace prefix, also in the opened namespace, and
the suffix Statement. Import the Library module that publishes
toDecompositionGroupOfEqTop instead of the source imports. Omit the simp
attribute, the open lines this statement does not need, and all other
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U001.Definitions

/-!
# The whole Galois group as decomposition group: coercion statement

A closed proposition: when the decomposition group of a valuation ring of
`L` over `K` is the whole group, the homomorphism
`toDecompositionGroupOfEqTop` followed by the coercion back to
`L ≃ₐ[K] L` is the identity.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- States the theorem `toDecompositionGroupOfEqTop_coe`. -/
def toDecompositionGroupOfEqTop_coeStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤)
    (sigma : L ≃ₐ[K] L),
    (toDecompositionGroupOfEqTop K A hA sigma : L ≃ₐ[K] L) = sigma

end Langlands.NYLL.LocalClassFieldTheory
