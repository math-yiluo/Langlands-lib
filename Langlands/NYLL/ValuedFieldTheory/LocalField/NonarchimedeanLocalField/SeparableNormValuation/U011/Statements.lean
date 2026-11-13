/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 13 November 2026: extracted the source theorem
LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable (inventory
M162.011) as the Prop-valued target
Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparableStatement.
The section telescope and the asserted type are unchanged. The source's
anonymous local instance M162.010, whose body is
FractionRing.liftAlgebra R (FractionRing S), is replaced by registering
FractionRing.liftAlgebra itself as a local instance. The source proof and the
other declarations are omitted. The imports are reduced to the source's two
Mathlib imports. The retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Normal closures of separable fraction-field extensions are Galois: statement target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
lines 240–256 (inventory M162.010 and M162.011).
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

attribute [local instance] FractionRing.liftAlgebra

/-- The normal closure of a finite separable extension of fraction fields is
Galois without assuming that the base fraction field is perfect.  Mathlib's
default instance uses perfectness because it treats arbitrary finite
extensions; here separability is precisely the available hypothesis. -/
def ringNormalClosure_isGalois_of_isSeparableStatement
    (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] : Prop :=
  IsGalois (FractionRing R)
    (FractionRing (Ring.NormalClosure R S))

end Langlands.NYLL.LocalClassFieldTheory
