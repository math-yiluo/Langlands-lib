/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Action.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U002.Proofs

/-!
# NYLL M101.008: the relative coset action on fixed-field units

Adapted by Worker 213 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:151–233`.
Modifications: isolate M101.008 and its private M101.007 prerequisite, prefix
its namespace with `Langlands.NYLL`, use focused published imports, and prove
the exact `Statement` target. Rename the private prerequisite and expose the
Prop definitions before rewriting. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology ClassFormation

noncomputable section

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

private theorem quotientRepresentative_apply_val_local
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


theorem relativeCosetAction_abstractRelativeFixedFieldUnit_val
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (x : Additive (abstractRelativeFixedField k Ω hLK)ˣ)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    relativeCosetAction_abstractRelativeFixedFieldUnit_valStatement
      k Ω K L hLK hnormal x q := by
  unfold relativeCosetAction_abstractRelativeFixedFieldUnit_valStatement
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [relativeCosetAction_mk]
  change σ.1 ((Additive.toMul x :
      (abstractRelativeFixedField k Ω hLK)ˣ) : Ω) = _
  exact quotientRepresentative_apply_val_local
    k Ω K L hLK hnormal σ
      (Additive.toMul x : (abstractRelativeFixedField k Ω hLK)ˣ)

end
end Langlands.NYLL.LocalClassFieldTheory
