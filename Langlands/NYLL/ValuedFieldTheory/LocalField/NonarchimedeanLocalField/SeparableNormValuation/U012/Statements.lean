/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 13 November 2026: extracted the source theorem
LocalClassFieldTheory.relNorm_eq_pow_inertiaDeg_of_isSeparable (inventory
M162.012) as the Prop-valued target
Langlands.NYLL.LocalClassFieldTheory.relNorm_eq_pow_inertiaDeg_of_isSeparableStatement.
The section telescope, the local instance attribute on FractionRing.liftAlgebra
and the asserted equation are unchanged. The source proof and the other
declarations are omitted. The imports are reduced to the source's two Mathlib
imports. The retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Relative norm of a maximal ideal in a separable extension: statement target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
lines 267–283 (inventory M162.012).
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

attribute [local instance] FractionRing.liftAlgebra

/-- Relative ideal norm of a maximal ideal in a finite separable extension.
This is the separable replacement for mathlib's perfect-base theorem and is
proved by the same normal-closure descent. -/
def relNorm_eq_pow_inertiaDeg_of_isSeparableStatement
    (R : Type u) (S : Type v)
    [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p]
    [P.IsMaximal] [p.IsMaximal] : Prop :=
  Ideal.relNorm R P = p ^ P.inertiaDeg R

end Langlands.NYLL.LocalClassFieldTheory
