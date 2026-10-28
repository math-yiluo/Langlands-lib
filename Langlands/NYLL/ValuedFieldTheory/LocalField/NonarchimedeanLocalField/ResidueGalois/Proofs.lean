/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.Statements

/-!
# Residue evaluation and base-residue fixedness

Adapted by Worker 761 from NYLL M160.002 and M160.004 on 28 October 2026.
The namespace is prefixed by `Langlands.NYLL`; each theorem proves its published
closed statement target over an arbitrary universe. The source's ambient-field
`rfl` step for base integers is replaced by the published forward evaluation of
the integer-ring restriction, and the source's `ResidueExtension` alias is replaced
by Mathlib's `IsLocalRing.ResidueField.algebraMap_residue`. The `@[simp]` attribute
is not retained. See the paired Markdown for correspondence and attribution.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The residue-field equivalence sends the residue class of an integer to the residue
class of its image under the integer-ring restriction. This proves the closed statement
target for NYLL M160.002. -/
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_residue :
    GaloisGroupResidueFieldEquivOfIsIntegralClosureResidueStatement.{u} := by
  intro K L _ _ _ _ _ _ _ σ x
  exact IsLocalRing.ResidueField.map_residue
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ : 𝒪[L] →+* 𝒪[L]) x

/-- The residue-field equivalence fixes the image of the base residue field under the
canonical residue algebra map. This proves the closed statement target for NYLL M160.004. -/
theorem galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap :
    GaloisGroupResidueFieldEquivOfIsIntegralClosureAlgebraMapStatement.{u} := by
  intro K L _ _ _ _ _ _ _ σ x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  rw [IsLocalRing.ResidueField.algebraMap_residue,
    galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L σ]
  refine congrArg (IsLocalRing.residue 𝒪[L]) (Subtype.ext ?_)
  rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L σ]
  exact σ.commutes (a : K)

end Langlands.NYLL.LocalFieldTheory
