/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Definitions
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.U001.Proofs

/-!
# The Galois refinement of a finite intermediate field

Modified by Worker 5264, 15 November 2026: extract the definition M033.005
`FiniteIntermediateField.galoisRefinement` and the instance M033.007
`FiniteIntermediateField.galoisRefinement_normal` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by focused published imports,
and omit the rest of the source file. The source proof terms
`M.normalCoreField_le` and `M.extensionSubgroup_normalCoreField` (the
unpublished proofs of M033.002 and M033.004) are replaced by their source
proofs written inline. The binders, docstrings and data are unchanged. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Every finite intermediate field admits a finite Galois refinement once
the bottom extension is normal. -/
def galoisRefinement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    FiniteIntermediateField E K where
  field := M.normalCoreField
  above := by
    intro e he
    let eK : K.toSubgroup := ⟨e, M.below (M.above he)⟩
    have heE : eK ∈ extensionSubgroup K E (M.above.trans M.below) :=
      (mem_extensionSubgroup_iff K E (M.above.trans M.below) eK).2 he
    have hle : extensionSubgroup K E (M.above.trans M.below) ≤
        extensionSubgroup K M.field M.below := by
      intro x hx
      apply (mem_extensionSubgroup_iff K M.field M.below x).2
      exact M.above
        ((mem_extensionSubgroup_iff K E (M.above.trans M.below) x).1 hx)
    have heCore : eK ∈ (extensionSubgroup K M.field M.below).normalCore :=
      (Subgroup.normal_le_normalCore.mpr hle) heE
    exact ⟨eK, heCore, rfl⟩
  below := by
    rintro g ⟨k, _, rfl⟩
    exact k.2
  finite := by
    let H := extensionSubgroup K M.field M.below
    let : H.FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _ H M.finite
    let : H.normalCore.FiniteIndex := inferInstance
    have hcore : extensionSubgroup K M.normalCoreField
        (show (M.normalCoreField).toSubgroup ≤ K.toSubgroup by
          rintro g ⟨k, _, rfl⟩
          exact k.2) =
        (extensionSubgroup K M.field M.below).normalCore := by
      ext k
      constructor
      · intro hk
        obtain ⟨k', hk', hk'n⟩ := hk
        have hk'eq : k' = k := by
          apply Subtype.ext
          exact hk'n
        simpa [hk'eq] using hk'
      · intro hk
        exact ⟨k, hk, rfl⟩
    rw [hcore]
    infer_instance

/-- The subgroup representing a Galois refinement is normal. -/
instance galoisRefinement_normal [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] :
    (extensionSubgroup K (M.galoisRefinement).field
      (M.galoisRefinement).below).Normal := by
  have hcore : extensionSubgroup K M.normalCoreField
      (show (M.normalCoreField).toSubgroup ≤ K.toSubgroup by
        rintro g ⟨k, _, rfl⟩
        exact k.2) =
      (extensionSubgroup K M.field M.below).normalCore := by
    ext k
    constructor
    · intro hk
      obtain ⟨k', hk', hk'n⟩ := hk
      have hk'eq : k' = k := by
        apply Subtype.ext
        exact hk'n
      simpa [hk'eq] using hk'
    · intro hk
      exact ⟨k, hk, rfl⟩
  change (extensionSubgroup K M.normalCoreField
    (show (M.normalCoreField).toSubgroup ≤ K.toSubgroup by
      rintro g ⟨k, _, rfl⟩
      exact k.2)).Normal
  rw [hcore]
  infer_instance

end FiniteIntermediateField

end groupTheoreticRefinements

end

end Langlands.NYLL.ClassFormation
