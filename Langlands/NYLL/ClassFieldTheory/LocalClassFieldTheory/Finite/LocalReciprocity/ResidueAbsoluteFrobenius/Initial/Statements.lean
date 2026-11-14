/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.Initial.Definitions

/-!
# Finite local reciprocity: Frobenius on an infinite residue extension (initial target)

Modified by Worker 123: replace the source theorem M168.008 of the pinned NYLL
`ResidueAbsoluteFrobenius` source by a Prop-valued `Statement` definition in the
`Langlands.NYLL` namespace, under the source's `variable` block so that the
target keeps the source theorem's complete parameter telescope (including the
section hypothesis `[IsGalois k Omega]`) and universes. The source proof is
omitted. The source theorems M168.006, M168.007 and M168.009, which mention the
later data command M168.005, are not part of this module. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
variable (k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [IsGalois k Omega]

/-- Target of M168.008: arithmetic Frobenius on an algebraic Galois extension
restricts to arithmetic Frobenius on every finite Galois intermediate field. -/
def restrictNormalHom_frobeniusAlgEquivOfAlgebraicStatement
    (E : FiniteGaloisIntermediateField k Omega) : Prop :=
  AlgEquiv.restrictNormalHom E
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) =
    FiniteField.frobeniusAlgEquivOfAlgebraic k E

end
end Langlands.NYLL.LocalClassFieldTheory
