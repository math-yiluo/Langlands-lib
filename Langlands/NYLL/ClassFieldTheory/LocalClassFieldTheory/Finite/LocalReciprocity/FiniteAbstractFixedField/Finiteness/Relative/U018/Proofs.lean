/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.Relative.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U024.Proofs

/-!
# NYLL M099.018: relative finite-dimensionality

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:306–335`.
Modifications: isolate this proof, prefix its namespace with `Langlands.NYLL`,
use focused published imports, and state its exact published `Statement` target.
The proof body is unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology ClassFormation

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

theorem abstractFixedField_relativeFiniteDimensional
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    abstractFixedField_relativeFiniteDimensionalStatement
      k Ω K L hLK hKfinite hLKfinite := by
  let : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
  let : IsScalarTower k (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)) :=
    hKfinite
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) := hLKfinite
  let : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) L (le_baseField L)) :=
    FiniteGaloisSubextension.finite_extension_trans hLK (le_baseField K)
  let : FiniteDimensional k (abstractFixedField k Ω L) :=
    abstractFixedField_finiteDimensional k Ω L inferInstance
  exact FiniteDimensional.right k
    (abstractFixedField k Ω K) (abstractFixedField k Ω L)

end
end Langlands.NYLL.LocalClassFieldTheory
