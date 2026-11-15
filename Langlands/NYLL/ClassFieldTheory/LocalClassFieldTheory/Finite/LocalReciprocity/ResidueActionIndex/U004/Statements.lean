/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 15 November 2026:
Extract the statement of M244.004 (residueAlgActionOfEqTop_surjective,
lines 72–76) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
ResidueActionIndex.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop-valued
definition without its proof. The section variables K, L, their field and
algebra binders and [IsGalois K L], which Lean adds to this theorem's
signature, become leading universal binders. Add the Langlands.NYLL
namespace prefix, also in the opened namespace, and the suffix Statement.
Import the Library module that publishes residueAlgActionOfEqTop instead of
the source imports. Omit the open lines this statement does not need and
all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U003.Definitions

/-!
# Surjectivity of the residue action of the whole Galois group

A closed proposition: when the decomposition group of a valuation ring `A`
of a Galois extension `L / K` is the whole group, the residue action
`residueAlgActionOfEqTop` of `L ≃ₐ[K] L` on the selected residue field of
`A` is surjective.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

/-- States the theorem `residueAlgActionOfEqTop_surjective`. -/
def residueAlgActionOfEqTop_surjectiveStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤),
    Function.Surjective (residueAlgActionOfEqTop K A hA)

end Langlands.NYLL.LocalClassFieldTheory
