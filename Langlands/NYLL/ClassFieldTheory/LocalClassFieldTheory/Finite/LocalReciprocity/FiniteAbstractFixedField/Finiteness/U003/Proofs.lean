/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M099.003 (ambientQuotientFiniteOfAbstractFinite)
from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published FiniteAbstractFixedField
Finiteness Statements module. Merge the source namespace openings into one
line, omit the unused `open RamificationTheory KummerTheory`, keep the
noncomputable section, the section variable line, `omit [IsGalois k Ω] in`
and the docstring, and state the theorem as the published Statement applied
to the source parameters. The proof is unchanged. The original LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.Statements

/-!
# Finite abstract quotient gives a finite ambient Galois quotient

The proof that finiteness of the quotient of the distinguished base by an
abstract closed subgroup gives finiteness of the ambient absolute Galois
group modulo the same subgroup.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open CyclicCohomology ClassFormation
noncomputable section
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

omit [IsGalois k Ω] in
/-- Absolute finiteness in the abstract class-formation quotient presentation gives a
finite quotient of the ambient absolute Galois group by the same subgroup. -/
theorem ambientQuotientFiniteOfAbstractFinite
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))) :
    ambientQuotientFiniteOfAbstractFiniteStatement k Ω H hfinite := by
  apply Nat.finite_of_card_ne_zero
  change H.toSubgroup.index ≠ 0
  rw [← Subgroup.relIndex_top_right]
  change (extensionSubgroup (baseField (Gal(Ω/k))) H
    (le_baseField H)).index ≠ 0
  exact @Subgroup.index_ne_zero_of_finite
    (baseField (Gal(Ω/k))).toSubgroup _
    (extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))
    hfinite

end
end Langlands.NYLL.LocalClassFieldTheory
