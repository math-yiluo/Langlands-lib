/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 123 and Worker 721 (2026-11): extract the M168.009
proof (source lines 161-177) from the pinned source at
fbd320cd8b1b06487c58227e92eb135794267709; prefix its namespace by
Langlands.NYLL, import the M168.007 and M168.008 proof modules (and through
them the published Prop target), and state the theorem with
that exact target as its type. The source proof is kept, with the two
rewrite lemmas passed through `show` of their unfolded `Statement` types. Retained license
and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.U007.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.U008.Proofs

/-!
# M168.009: the absolute Frobenius at one (proof)
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

/-- The distinguished element `1 ∈ ℤ̂` acts on the whole algebraic Galois
extension by the actual arithmetic Frobenius. -/
@[simp]
theorem residueAbsoluteFrobenius_one :
    residueAbsoluteFrobenius_oneStatement k Omega := by
  apply (InfiniteGalois.continuousMulEquivToLimit k Omega).injective
  apply Subtype.ext
  funext E
  change AlgEquiv.restrictNormalHom E.unop
      (residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd (1 : ZHat))) =
    AlgEquiv.restrictNormalHom E.unop
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)
  rw [show AlgEquiv.restrictNormalHom E.unop
        (residueAbsoluteFrobenius k Omega (Multiplicative.ofAdd (1 : ZHat))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E.unop from
    restrictNormalHom_residueAbsoluteFrobenius_one k Omega E.unop,
    show AlgEquiv.restrictNormalHom E.unop
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E.unop from
    restrictNormalHom_frobeniusAlgEquivOfAlgebraic k Omega E.unop]

end
end Langlands.NYLL.LocalClassFieldTheory
