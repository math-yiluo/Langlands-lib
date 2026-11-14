/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.Absolute.Definitions

/-!
# Finite local reciprocity: Frobenius on an infinite residue extension (absolute targets)

Modified by Worker 123: replace the source theorems M168.006, M168.007 and
M168.009 of the pinned NYLL `ResidueAbsoluteFrobenius` source by Prop-valued
`Statement` definitions in the `Langlands.NYLL` namespace, under the source's
`variable` block, so that every target keeps the source theorem's complete
parameter telescope and universes. The target of the source `@[simp]` theorem
M168.009 is reducible (`abbrev`). Source proofs are omitted. See the paired
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

/-- Target of M168.006: restricting the assembled Frobenius to a finite Galois
intermediate field gives exactly the finite Frobenius coordinate. -/
def restrictNormalHom_residueAbsoluteFrobeniusStatement
    (z : ZHatMul) (E : FiniteGaloisIntermediateField k Omega) : Prop :=
  AlgEquiv.restrictNormalHom E (residueAbsoluteFrobenius k Omega z) =
    finiteResidueFrobeniusIntermediate k Omega E z

/-- Target of M168.007: the element `1 ∈ ℤ̂` gives the actual arithmetic
Frobenius on every finite Galois residue subextension. -/
def restrictNormalHom_residueAbsoluteFrobenius_oneStatement
    (E : FiniteGaloisIntermediateField k Omega) : Prop :=
  AlgEquiv.restrictNormalHom E
      (residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd (1 : ZHat))) =
    FiniteField.frobeniusAlgEquivOfAlgebraic k E

/-- Target of M168.009: the distinguished element `1 ∈ ℤ̂` acts on the whole
algebraic Galois extension by the actual arithmetic Frobenius. -/
abbrev residueAbsoluteFrobenius_oneStatement : Prop :=
  residueAbsoluteFrobenius k Omega
      (Multiplicative.ofAdd (1 : ZHat)) =
    FiniteField.frobeniusAlgEquivOfAlgebraic k Omega

end
end Langlands.NYLL.LocalClassFieldTheory
