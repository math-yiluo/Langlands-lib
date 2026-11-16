/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws.FieldImageConjugate.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U011.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs

/-!
# NYLL M027.001: conjugating an abstract field does not change its degree image

Modified by Worker 5264, 15 November 2026: prove the published target
`DegreeData.fieldImage_conjugateStatement` (M027.001) by the source proof of
`DegreeData.fieldImage_conjugate` in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, rewrite with local copies
`hK`, `hKσ` of the published `...Statement`-typed `fieldImage_eq_map` and
`hmem` of `conjugateClosedSubgroup_mem`, replace the source imports by
published modules and omit the unused opens and variable declarations and
the rest of the source file. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Conjugating an abstract field does not change its degree image. -/
theorem DegreeData.fieldImage_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (D : DegreeData G) (K : ClosedSubgroup G) (σ : G) :
    DegreeData.fieldImage_conjugateStatement D K σ := by
  show D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K
  have hKσ : D.fieldImage (conjugateClosedSubgroup K σ) =
      (conjugateClosedSubgroup K σ).toSubgroup.map D.degree.toMonoidHom :=
    D.fieldImage_eq_map (conjugateClosedSubgroup K σ)
  have hK : D.fieldImage K = K.toSubgroup.map D.degree.toMonoidHom :=
    D.fieldImage_eq_map K
  have hmem : ∀ x : G, x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K :=
    fun x => conjugateClosedSubgroup_mem K σ x
  rw [hKσ, hK]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    let k : K.toSubgroup :=
      ⟨σ * x * σ⁻¹, (hmem x).mp hx⟩
    refine ⟨k.1, k.2, ?_⟩
    simp [k, map_mul, mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    let x : G := σ⁻¹ * k * σ
    have hx : x ∈ conjugateClosedSubgroup K σ := by
      rw [hmem]
      change σ * x * σ⁻¹ ∈ K.toSubgroup
      simpa [x, mul_assoc] using hk
    refine ⟨x, hx, ?_⟩
    simp [x, map_mul, mul_assoc, mul_comm]

end

end Langlands.NYLL.ClassFormation
