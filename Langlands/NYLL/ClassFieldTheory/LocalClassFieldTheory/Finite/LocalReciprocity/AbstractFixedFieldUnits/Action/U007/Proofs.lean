/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Action.Statements

/-!
# NYLL M101.007: quotient representatives act by ambient restriction

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:151–202`.
Modifications: isolate this theorem, prefix its namespace with `Langlands.NYLL`,
use the focused published statement import, and state the exact `Statement`
target. A leading `change` exposes that target; the source proof otherwise
remains unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology ClassFormation

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

theorem abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (σ : K.toSubgroup)
    (x : abstractRelativeFixedField k Ω hLK) :
    abstractExtensionQuotientEquivGaloisGroup_mk_apply_valStatement
      k Ω K L hLK hnormal σ x := by
  let := hnormal
  change σ.1 (x : Ω) = _
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  let H : ClosedSubgroup (Gal(Ω / abstractFixedField k Ω K)) :=
    closedFixingSubgroup (abstractFixedField k Ω K) Ω
      (abstractRelativeFixedField k Ω hLK)
  let : H.toSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  have hq :
      abstractExtensionQuotientEquivAmbient k Ω K L hLK hnormal
          (QuotientGroup.mk' (extensionSubgroup K L hLK) σ) =
        QuotientGroup.mk'
          (abstractRelativeFixedField k Ω hLK).fixingSubgroup
          (abstractSubgroupEquivGaloisGroup k Ω K σ) := by
    rfl
  rw [abstractExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
    MulEquiv.trans_apply]
  change σ.1 (x : Ω) =
    ((((IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_fixingSubgroup
        (abstractRelativeFixedField k Ω hLK))).autCongr
      (InfiniteGalois.normalAutEquivQuotient
        (closedFixingSubgroup (abstractFixedField k Ω K) Ω
          (abstractRelativeFixedField k Ω hLK))
        ((abstractSubgroupEquivGaloisGroup k Ω K σ :
            Gal(Ω / abstractFixedField k Ω K)) :
          Gal(Ω / abstractFixedField k Ω K) ⧸
            (abstractRelativeFixedField k Ω hLK).fixingSubgroup))) x :
      abstractRelativeFixedField k Ω hLK) : Ω)
  rw [InfiniteGalois.normalAutEquivQuotient_apply,
    AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change σ.1 (x : Ω) =
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField H.toSubgroup)
      (abstractSubgroupEquivGaloisGroup k Ω K σ))
      ⟨(x : Ω), _⟩ : IntermediateField.fixedField H.toSubgroup) : Ω)
  rw [AlgEquiv.restrictNormalHom_apply]
  rfl

end
end Langlands.NYLL.LocalClassFieldTheory
