/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 13 November 2026 UTC:
Extract only the proof of M096.012 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the published SeparableUnitsNorm.Embedding
Statements module and open only LocalFieldTheory. Keep the source section
variables and omit clause, omit the unused local instances M096.010-011, and
state the theorem as the published Statement applied to the source
parameters. The proof is unchanged. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm.Embedding.Statements

/-!
# Norm invariance under an embedded field realization

The proof that the unit-level norm of `x : Lˣ` to `K` equals the norm of its
image in the realization `AlgHom.fieldRange i` of `L` inside `Ω`.
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
/-- The field norm is invariant under an algebra equivalence, at unit level. -/
theorem normUnits_embeddedExtensionAlgEquiv (x : Lˣ) :
    normUnits_embeddedExtensionAlgEquivStatement K Ω L i x := by
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv
    (AlgEquiv.ofInjectiveField i) (x : L)

end EmbeddedFiniteGaloisExtension

end Langlands.NYLL.LocalClassFieldTheory
