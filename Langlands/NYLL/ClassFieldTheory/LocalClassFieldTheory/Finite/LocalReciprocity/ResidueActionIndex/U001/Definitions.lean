/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Extract only M244.001 (toDecompositionGroupOfEqTop) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
ResidueActionIndex.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, also in the opened namespace. Import the Library module
that publishes decompositionGroup instead of the source imports. Omit the
open lines this definition does not need and all other declarations. The
binders, type and body are otherwise the source text.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions

/-!
# The whole Galois group as decomposition group

When the decomposition group of a valuation ring of a Galois extension
`L / K` is the whole group, every automorphism of `L / K` is viewed as an
element of the decomposition group, by a monoid homomorphism.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
  [IsGalois K L]

/-- View every ambient Galois automorphism as a decomposition-group element
when the chosen extension valuation has full decomposition group.  This is
kept generic in the Galois ambient field: the ambient field is the
separable closure, not the algebraic closure (the latter need not be Galois
over an imperfect local field). -/
noncomputable def toDecompositionGroupOfEqTop
    (A : _root_.ValuationSubring L)
    (hA : decompositionGroup K A = ⊤) :
    (L ≃ₐ[K] L) →* decompositionGroup K A where
  toFun sigma := ⟨sigma, by rw [hA]; exact Subgroup.mem_top sigma⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

end

end Langlands.NYLL.LocalClassFieldTheory
