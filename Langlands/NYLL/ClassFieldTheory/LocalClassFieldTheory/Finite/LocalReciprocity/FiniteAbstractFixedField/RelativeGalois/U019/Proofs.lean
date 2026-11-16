/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.RelativeGalois.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U024.Proofs

/-!
# NYLL M099.019: finite-dimensionality in the relative field presentation

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:306–363`.
Modifications: isolate M099.019, prefix its namespace with `Langlands.NYLL`,
use focused published imports and its exact published `Statement` target.
Include M099.018 privately as `relativeFiniteDimensional_local`, since that
prerequisite proof is not yet published, and call it in place of the source name.
Both source proof bodies otherwise remain unchanged. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology ClassFormation

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

private theorem relativeFiniteDimensional_local
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    letI : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
      RingHom.toAlgebra
        (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) := by
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

theorem abstractRelativeFixedField_finiteDimensional
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    abstractRelativeFixedField_finiteDimensionalStatement
      k Ω K L hLK hKfinite hLKfinite := by
  let : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
  let : FiniteDimensional (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) :=
    relativeFiniteDimensional_local
      k Ω K L hLK hKfinite hLKfinite
  let e : abstractFixedField k Ω L ≃ₗ[abstractFixedField k Ω K]
      abstractRelativeFixedField k Ω hLK :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finiteDimensional

end
end Langlands.NYLL.LocalClassFieldTheory
