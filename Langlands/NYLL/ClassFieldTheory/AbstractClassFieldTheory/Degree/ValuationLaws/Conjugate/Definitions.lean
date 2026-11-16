/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U011.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U002.Proofs

/-!
# The conjugate of a residue-finite abstract field

Modified by Worker 5264, 15 November 2026: port the source definition
M027.002 `DegreeData.FiniteResidueAbstractField.conjugate` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL` and replace the source imports by focused published imports.
The proof of the field `finiteResidueQuotient` rewrites with the theorem
`D.fieldImage_conjugate K.field σ` (M027.001), whose proof is not published;
the rewrite now uses a local `himage` stating that equation, proved by the
source proof of `DegreeData.fieldImage_conjugate` at `K.field`. In that proof
the two rewrites with the published `...Statement`-typed `fieldImage_eq_map`
are made with local copies `hKσ`, `hK`, and the rewrite with
`conjugateClosedSubgroup_mem` with a local copy `hmem`. The docstring, the
binders (the definition binds its own `G`), the field `field` and the rest of
the field proof are unchanged. Omit the source opens and variable
declarations, which this definition does not use, and the rest of the source
file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

/-- Conjugate a field whose actual absolute residue quotient is finite.
The transported field remains in the same residue-finite boundary because
conjugation does not change the degree image. -/
noncomputable def DegreeData.FiniteResidueAbstractField.conjugate
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    DegreeData.FiniteResidueAbstractField D where
  field := conjugateClosedSubgroup K.field σ
  finiteResidueQuotient := by
    have himage : D.fieldImage (conjugateClosedSubgroup K.field σ) =
        D.fieldImage K.field := by
      have hKσ : D.fieldImage (conjugateClosedSubgroup K.field σ) =
          (conjugateClosedSubgroup K.field σ).toSubgroup.map
            D.degree.toMonoidHom :=
        D.fieldImage_eq_map (conjugateClosedSubgroup K.field σ)
      have hK : D.fieldImage K.field =
          K.field.toSubgroup.map D.degree.toMonoidHom :=
        D.fieldImage_eq_map K.field
      have hmem : ∀ x : G, x ∈ conjugateClosedSubgroup K.field σ ↔
          σ * x * σ⁻¹ ∈ K.field :=
        fun x => conjugateClosedSubgroup_mem K.field σ x
      rw [hKσ, hK]
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        let k : K.field.toSubgroup :=
          ⟨σ * x * σ⁻¹, (hmem x).mp hx⟩
        refine ⟨k.1, k.2, ?_⟩
        simp [k, map_mul, mul_assoc]
      · rintro ⟨k, hk, rfl⟩
        let x : G := σ⁻¹ * k * σ
        have hx : x ∈ conjugateClosedSubgroup K.field σ := by
          rw [hmem]
          change σ * x * σ⁻¹ ∈ K.field.toSubgroup
          simpa [x, mul_assoc] using hk
        refine ⟨x, hx, ?_⟩
        simp [x, map_mul, mul_assoc, mul_comm]
    unfold DegreeData.residueQuotient
    rw [himage]
    exact K.finiteResidueQuotient

end

end Langlands.NYLL.ClassFormation
