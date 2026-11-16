/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.RelativeGalois.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Equivalences.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U024.Proofs

/-!
# NYLL M099.020: abstract degree equals concrete fixed-field degree

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:367–404`.
Modifications: isolate M099.020, prefix its namespace with `Langlands.NYLL`,
use focused published imports and its exact published `Statement` target.
Include unpublished prerequisites M099.018, M099.019 and M099.012 under
private names. Replace the M010.092 index/degree bridge by the private
`degree_eq_index_local`, proved by definitional reduction in the required
direction. The main cardinality calculation otherwise follows the source.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
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

private theorem relativePresentationFiniteDimensional_local
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
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

private theorem relativeFixedFieldGalois_local
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    IsGalois (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (abstractRelativeFixedField k Ω hLK)).1
  exact abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal

omit [IsGalois k Ω] in
private theorem degree_eq_index_local
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
      (extensionSubgroup K L hLK).index := by
  rfl

theorem finiteAbstractExtension_degree_eq_finrank
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hKfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K)))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)) :
    finiteAbstractExtension_degree_eq_finrankStatement
      k Ω K L hLK hnormal hKfinite hLKfinite := by
  let := hnormal
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) := hLKfinite
  let : FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    relativePresentationFiniteDimensional_local
      k Ω K L hLK hKfinite hLKfinite
  let : IsGalois (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    relativeFixedFieldGalois_local k Ω K L hLK hnormal
  calc
    ((DegreeData.FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
        (extensionSubgroup K L hLK).index :=
      degree_eq_index_local k Ω K L hLK
    _ = Nat.card
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      Subgroup.index_eq_card (extensionSubgroup K L hLK)
    _ = Nat.card (Gal(abstractRelativeFixedField k Ω hLK/abstractFixedField k Ω K)) :=
      Nat.card_congr
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).toEquiv
    _ = Module.finrank (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) :=
      IsGalois.card_aut_eq_finrank
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)

end
end Langlands.NYLL.LocalClassFieldTheory
