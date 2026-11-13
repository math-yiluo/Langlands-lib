/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Subquotient

/-!
# Principal-unit graded-piece data

Adapted by Worker 321 from NYLL M120.038–039 and M120.041–042 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Modifications: prefix the
namespace by `Langlands.NYLL`, isolate the listed data, and import their
paired subquotient module in place of the original Mathlib import list.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

open scoped BigOperators

namespace DiscreteValuationField

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- The principal-unit graded piece `U^n/U^{n+1}`. -/
def principalUnitGradedPiece (n : ℕ) : Type u :=
  U.principalUnitSubquotient n (n + 1)

/--
Equips the target with its canonical `Group` structure, namely `Group (U.principalUnitGradedPiece
n)`.
-/
instance principalUnitGradedPieceGroup
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    Group (U.principalUnitGradedPiece n) := by
  change Group (U.principalUnitSubquotient n (n + 1))
  infer_instance

/-- Explicit identification of a graded piece with its named adjacent
subquotient. -/
def principalUnitGradedPieceEquivSubquotient
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    U.principalUnitGradedPiece n ≃*
      U.principalUnitSubquotient n (n + 1) := by
  change U.principalUnitSubquotient n (n + 1) ≃*
    U.principalUnitSubquotient n (n + 1)
  exact MulEquiv.refl _

/-- The type in `Finite (U.principalUnitGradedPiece n)` is finite. -/
noncomputable instance principalUnitGradedPieceFinite
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal]
    [Finite (U.principalUnitSubquotient n (n + 1))] :
    Finite (U.principalUnitGradedPiece n) :=
  Finite.of_equiv (U.principalUnitSubquotient n (n + 1))
    (U.principalUnitGradedPieceEquivSubquotient n).symm.toEquiv

end AntitoneSubgroupFiltration

end DiscreteValuationField

end Langlands.NYLL.LocalFieldTheory
