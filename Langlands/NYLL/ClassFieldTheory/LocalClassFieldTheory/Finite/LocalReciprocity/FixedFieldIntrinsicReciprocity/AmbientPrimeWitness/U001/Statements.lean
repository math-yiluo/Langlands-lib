/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the asserted type of M284.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeWitness.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and package all ten original binders inside a closed Prop-valued
definition, preserving their order, binder kinds, the source's universe-zero
group types and the orientation of both equations. The named hypothesis
hprime becomes an anonymous premise of the same type.
Replace the source imports by the single Mathlib module that defines
abelianizations and their functorial equivalences. Defer the truth proof;
install no instance or simp registration. Omit the original noncomputable
section, the unused namespace openings and all other declarations of the
module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Transport of an identified abelianized prime value

The closed assertion that moving an abelianized value back through one
quotient equivalence and forward through another recovers the forward
image of the abelianized ambient element that it was identified with.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Transporting an identified abelianized prime value back through one
quotient equivalence and forward through another preserves its target. -/
def abelianizationCongr_symm_eq_primeTargetStatement : Prop :=
  ∀ {Q₀ G₀ G : Type}
    [Group Q₀] [Group G₀] [Group G]
    (q₀ : Q₀ ≃* G₀)
    (qE : Q₀ ≃* G)
    (qAmbient : Q₀)
    (r : Additive (Abelianization G₀)),
    r =
        Additive.ofMul
          (q₀.abelianizationCongr
            (Abelianization.of qAmbient)) →
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul r)) =
      qE.abelianizationCongr
        (Abelianization.of qAmbient)

end Langlands.NYLL.LocalClassFieldTheory
