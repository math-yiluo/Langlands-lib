/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 13 November 2026 UTC:
Extract only the proof of M096.013 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published SeparableUnitsNorm.Embedding
Statements module and the published M096.012 proof module, and open only
LocalFieldTheory. Keep the source section variables and omit clause, omit the
unused local instances M096.010-011, and state the theorem as the published
Statement applied to the source parameters. The proof is unchanged. The
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Embedding.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Embedding.U012.Proofs

/-!
# Norm subgroups of an embedded field realization

The proof that the norm subgroup of `Kˣ` attached to the realization
`AlgHom.fieldRange i` of `L` inside `Ω` equals the norm subgroup attached
to `L`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

section EmbeddedFiniteGaloisExtension

variable (L : Type) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] Ω)

omit [IsGalois K Ω] [FiniteDimensional K L] [IsGalois K L] in
/-- The ordinary norm subgroups are independent of the chosen realization of
the finite extension inside the ambient Galois extension. -/
theorem localNormSubgroup_fieldRange_eq :
    localNormSubgroup_fieldRange_eqStatement K Ω L i := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let z : Lˣ := Units.mapEquiv
      (AlgEquiv.ofInjectiveField i).symm.toMulEquiv y
    refine ⟨z, ?_⟩
    have hz : Units.mapEquiv
        (AlgEquiv.ofInjectiveField i).toMulEquiv z = y := by
      exact (Units.mapEquiv
        (AlgEquiv.ofInjectiveField i).toMulEquiv).apply_symm_apply y
    rw [← hz, normUnits_embeddedExtensionAlgEquiv]
  · rintro ⟨x, rfl⟩
    refine ⟨Units.mapEquiv
      (AlgEquiv.ofInjectiveField i).toMulEquiv x, ?_⟩
    exact normUnits_embeddedExtensionAlgEquiv K Ω L i x

end EmbeddedFiniteGaloisExtension

end Langlands.NYLL.LocalClassFieldTheory
