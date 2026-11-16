/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField.DegreeZeroCommutes.Statements

/-!
# NYLL M038.003: normalized degrees of powers of a degree-one Frobenius element

Modified by Worker 5264, 15 November 2026: prove the published target
`Langlands.NYLL.PortInternal.M038.d003Statement` (M038.003) by the source
proof of the private theorem
`DegreeData.extensionNormalizedDegree_pow_of_degreeOne` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, under the published name
`Langlands.NYLL.PortInternal.M038.d003`. Give the theorem the published
proposition as its type, begin the proof with `show` stating it unfolded,
and rewrite with the local fact `hfrob`, proved by
`(Exists.choose_spec φ.2).2` as the unpublished M014.014
`extensionNormalizedDegree_frobenius_eq_pow` is in the source, in place of
that lemma. Replace the source import by the published statement module and
omit the unused opens and the rest of the source file. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section degreeOnePowerFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The private source theorem
`DegreeData.extensionNormalizedDegree_pow_of_degreeOne`: the normalized
degree of the `n`-th power of a Frobenius element of exponent one is the
`n`-th power of the generator. -/
theorem _root_.Langlands.NYLL.PortInternal.M038.d003 (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) :
    Langlands.NYLL.PortInternal.M038.d003Statement D K L hLK φ hφ n := by
  show D.extensionNormalizedDegree K L hLK (φ.1 ^ n) =
    (Multiplicative.ofAdd (1 : ZHat)) ^ n
  have hfrob : D.extensionNormalizedDegree K L hLK φ.1 =
      (Multiplicative.ofAdd (1 : ZHat)) ^ D.frobeniusExponent K L hLK φ :=
    (Exists.choose_spec φ.2).2
  rw [map_pow, hfrob, hφ, pow_one]

end DegreeData

end degreeOnePowerFields

end

end Langlands.NYLL.ClassFormation
