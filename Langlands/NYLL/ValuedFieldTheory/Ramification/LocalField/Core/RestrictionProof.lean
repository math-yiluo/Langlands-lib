/-
NYLL source: Copyright (c) 2026 Naganori Yamaguchi
(https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0; Authors: Naganori Yamaguchi (assisted by OpenAI Codex).
Pinned commit: fbd320cd8b1b06487c58227e92eb135794267709.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.

Worker 296, 2026-11-13: derive an internal comparison with the published FLT
ring-action formalization, reusing Library declarations by Lean name. This is
an alternate proof route to NYLL M327.009, not a translation of M326. The
published HerbrandBridge transport and finite-sum helpers are reused directly;
its fixed-subring strategy is adapted to the NYLL chosen-valuation convention.
The FLT theorem attribution and notices remain in licenses/Anthropic-FLT/.
See the paired Markdown for the complete proof route and source correspondence.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.FixedFieldTransport
import Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.AutCongrProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Proofs

noncomputable section

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory

/-- The actual local upper groups commute with restriction between nested
finite Galois subextensions of the separable closure. -/
theorem localUpperRamificationGroup_map_restrict :
    localUpperRamificationGroup_map_restrictStatement := by
  intro K _ _ _ _ E F hEF _ _ _ _ t
  let EF : IntermediateField K F := E.comap F.val
  let eEF : EF ≃ₐ[K] E :=
    { toFun := fun x => ⟨F.val x, x.property⟩
      invFun := fun x =>
        ⟨IntermediateField.inclusion hEF x, by
          change F.val (IntermediateField.inclusion hEF x) ∈ E
          exact x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply F.val.injective
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        rfl
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      commutes' := by
        intro x
        apply Subtype.ext
        rfl }
  let : IsGalois K EF := IsGalois.of_algEquiv eEF.symm
  let H : Subgroup Gal(F/K) := EF.fixingSubgroup
  let : H.Normal := by
    dsimp only [H]
    infer_instance
  let eFixed : IntermediateField.fixedField H ≃ₐ[K] E :=
    (IntermediateField.equivOfEq
      (IsGalois.fixedField_fixingSubgroup EF)).trans eEF
  have hrestrict :
      intermediateFieldRestrictNormalHom E F hEF =
        (AlgEquiv.autCongr eFixed).toMonoidHom.comp
          (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H)) := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply E.val.injective
    change
      E.val (intermediateFieldRestrictNormalHom E F hEF σ x) =
        E.val (((AlgEquiv.autCongr eFixed).toMonoidHom.comp
          (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H))) σ x)
    rw [intermediateFieldRestrictNormalHom_apply_val]
    simp only [eFixed, eEF, EF, H, IntermediateField.coe_val,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp,
      Function.comp_apply]
    symm
    exact congrArg F.val
      (AlgEquiv.restrictNormal_commutes σ
        (IntermediateField.fixedField H) (eFixed.symm x))
  rw [hrestrict, ← Subgroup.map_map,
    Langlands.NYLL.PortInternal.FltBridge.local_map_fixed K F H t]
  exact localUpperRamificationGroup_map_autCongr
    K (IntermediateField.fixedField H) E eFixed t

end Langlands.NYLL.RamificationTheory.LocalField
