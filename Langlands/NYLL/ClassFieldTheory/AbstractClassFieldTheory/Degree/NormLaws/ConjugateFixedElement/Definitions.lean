/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs

/-!
# The right conjugate of a fixed element

Modified by Worker 5264, 15 November 2026: port the source definition
M026.003 `conjugateFixedElement` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by a focused published import
(the proved M026.002 `conjugateClosedSubgroup_mem`, which also brings the
published `conjugateClosedSubgroup` and `ambientFixedAddSubgroup`), keep the
source opens, variable declaration, docstring, binders and construction with
its embedded proof unchanged, and omit the rest of the source file. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators Pointwise

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The right-conjugate `a^σ`, expressed through the left action of `G`. -/
def conjugateFixedElement [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) :
    ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ) := by
  refine ⟨A.ρ σ⁻¹ a.1, ?_⟩
  intro x
  let k : K.toSubgroup := ⟨σ * x.1 * σ⁻¹,
    (conjugateClosedSubgroup_mem K σ x.1).mp x.2⟩
  calc
    A.ρ x.1 (A.ρ σ⁻¹ a.1) = A.ρ (x.1 * σ⁻¹) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (σ⁻¹ * k.1) a.1 := by simp [k, mul_assoc]
    _ = A.ρ σ⁻¹ (A.ρ k.1 a.1) := by
      rw [map_mul]
      rfl
    _ = A.ρ σ⁻¹ a.1 := by rw [a.2 k]

end

end Langlands.NYLL.ClassFormation
