/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 123 and Worker 484 (2026-11): extract the M168.008
proof (source lines 138-159) from the pinned source at
fbd320cd8b1b06487c58227e92eb135794267709; prefix its namespace by
Langlands.NYLL, import its published Prop target, and state the theorem with
that exact target as its type. The proof script is unchanged. Retained license
and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.Initial.Statements

/-!
# M168.008: absolute Frobenius restricts to finite Frobenius (proof)
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

/-- Arithmetic Frobenius on an algebraic Galois extension restricts to
arithmetic Frobenius on every finite Galois intermediate field. -/
theorem restrictNormalHom_frobeniusAlgEquivOfAlgebraic
    (E : FiniteGaloisIntermediateField k Omega) :
    restrictNormalHom_frobeniusAlgEquivOfAlgebraicStatement k Omega E := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Omega).injective
  calc
    algebraMap E Omega
        ((AlgEquiv.restrictNormalHom E
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)) x) =
        FiniteField.frobeniusAlgEquivOfAlgebraic k Omega
          (algebraMap E Omega x) :=
      AlgEquiv.restrictNormal_commutes
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) E x
    _ = algebraMap E Omega
        (FiniteField.frobeniusAlgEquivOfAlgebraic k E x) := by
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
      exact (map_pow (algebraMap E Omega) x (Fintype.card k)).symm

end
end Langlands.NYLL.LocalClassFieldTheory
