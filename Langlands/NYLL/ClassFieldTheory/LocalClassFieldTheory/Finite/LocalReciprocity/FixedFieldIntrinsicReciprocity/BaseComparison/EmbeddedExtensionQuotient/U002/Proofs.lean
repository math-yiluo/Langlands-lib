/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement
of M274.002 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709, following the source proof.
Add the Langlands.NYLL namespace prefix and import only the U001 Proofs
module, which proves M274.001 and imports the statement. Omit the source's
local data jF, jI, EI, H₀, J₀, hRange and hJH, which the proof does not use
after the statement's own local data is unfolded, and name the M274.001
instance used hmem. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U001.Proofs

/-!
# Embedded extension quotients: image of the intrinsic extension subgroup

The proof of the published closed proposition that
`intrinsicBaseEquivAmbientEmbeddedField` maps the intrinsic extension subgroup
of an embedded finite Galois extension `E / F` onto the ambient extension
subgroup.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology

/-- The embedded-field base equivalence maps the intrinsic extension subgroup
for `E / F` onto the ambient subgroup fixing the field range of `E`. -/
theorem map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField :
    map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement := by
  intro K F E _ _ _ _ _ _ _ _ _ _ _ j
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  have hmem :=
    intrinsicExtensionSubgroup_iff_ambientEmbeddedField K F E j e
  ext sigma
  constructor
  · rintro ⟨tau, htau, rfl⟩
    exact (hmem tau).1 htau
  · intro hsigma
    let tau :
        (intrinsicAbstractBase F).toSubgroup :=
      psi.symm sigma
    refine ⟨tau, ?_, psi.apply_symm_apply sigma⟩
    apply (hmem tau).2
    have htauImage : psi tau = sigma :=
      psi.apply_symm_apply sigma
    rw [htauImage]
    exact hsigma

end Langlands.NYLL.LocalClassFieldTheory
