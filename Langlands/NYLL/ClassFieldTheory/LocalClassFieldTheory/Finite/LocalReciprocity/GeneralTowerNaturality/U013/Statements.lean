/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 30, 13 November 2026: extracted the source theorem
LocalClassFieldTheory.restrictNormalHom_eq_autCongr (inventory M262.013) as the
Prop-valued target
Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_eq_autCongrStatement.
The source proof is omitted. The telescope, the two local instances in the source
statement (including their proof term) and the asserted equation are unchanged.
The imports are reduced to Mathlib.FieldTheory.Normal.Defs.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.Normal.Defs

/-!
# Restriction along an algebra equivalence is conjugation: statement target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`,
lines 402–419 (inventory M262.013).
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

/-- When `L` is regarded as an `M`-algebra through the inverse of a
`K`-algebra equivalence, restriction from `L` to `M` is conjugation by that
equivalence. -/
def restrictNormalHom_eq_autCongrStatement
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K M]
    (e : L ≃ₐ[K] M) : Prop :=
    letI : Algebra M L := e.symm.toRingHom.toAlgebra
    letI : IsScalarTower K M L :=
      IsScalarTower.of_algebraMap_eq' (by
        apply RingHom.ext
        intro x
        exact (e.symm.commutes x).symm)
    (AlgEquiv.restrictNormalHom M :
        Gal(L / K) →* Gal(M / K)) =
      (AlgEquiv.autCongr e).toMonoidHom

end Langlands.NYLL.LocalClassFieldTheory
