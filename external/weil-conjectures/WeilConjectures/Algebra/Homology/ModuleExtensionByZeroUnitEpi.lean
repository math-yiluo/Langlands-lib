/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Adjunction.Triple
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- The extension-by-zero/restriction unit is epic.
Source: Stacks Project, Sheaves Lemma 00A7 (4).
Proof: the forgetful functor from opens over W to opens of X is fully faithful,
since the category of opens is thin. Hence its adjunction with intersection with W
has invertible unit. The counit of the induced restriction/direct-image adjunction
on modules is given by restriction along that unit, so it is invertible sectionwise.
The adjoint-triple criterion makes the chosen extension-by-zero/restriction unit
invertible as well. In particular each component is epic.
(blueprint: lem-sc-module-extension-by-zero-unit-epi) -/
theorem moduleExtensionByZero_unit_epi (X : RingedSpace.{u}) (W : Opens X)
    (G : SheafOfModules.{u} ((moduleRings X).over W)) :
    Epi ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app G) := by
  let R := moduleRings X
  let a := Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2
  let b := SheafOfModules.overPushforwardOverAdj (R := R) W
  have : (Over.forget W).Full := by
    constructor
    intro V V' f
    exact ⟨Over.homMk f (Subsingleton.elim _ _), rfl⟩
  have : IsIso (Over.forgetAdjStar W).unit := inferInstance
  have : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    change IsIso (M.val.presheaf.map ((Over.forgetAdjStar W).unit.app V.unop).op)
    infer_instance
  let t : Adjunction.Triple _ _ _ := ⟨a, b⟩
  have : IsIso a.unit := t.isIso_unit_iff_isIso_counit.mpr inferInstance
  infer_instance
end AlgebraicGeometry
