/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 123 and Worker 721 (2026-11): extract the M168.007
proof (source lines 126-136) from the pinned source at
fbd320cd8b1b06487c58227e92eb135794267709; prefix its namespace by
Langlands.NYLL, import the M168.006 and M167.013 proof modules (and through
them the published Prop target), and state the theorem with
that exact target as its type. The source proof is kept, with the
`Statement` definitions unfolded before its rewrite. Retained license
and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U013.Proofs

/-!
# M168.007: the profinite exponent one on finite subextensions (proof)
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

/-- The element `1 ∈ ℤ̂` gives the actual arithmetic Frobenius on every
finite Galois residue subextension. -/
theorem restrictNormalHom_residueAbsoluteFrobenius_one
    (E : FiniteGaloisIntermediateField k Omega) :
    restrictNormalHom_residueAbsoluteFrobenius_oneStatement k Omega E := by
  unfold restrictNormalHom_residueAbsoluteFrobenius_oneStatement
  have h := restrictNormalHom_residueAbsoluteFrobenius k Omega
    (Multiplicative.ofAdd (1 : ZHat)) E
  unfold restrictNormalHom_residueAbsoluteFrobeniusStatement at h
  rw [h]
  let : Finite E := Module.finite_of_finite k
  exact finiteResidueFrobeniusFromZHat_one k E

end
end Langlands.NYLL.LocalClassFieldTheory
