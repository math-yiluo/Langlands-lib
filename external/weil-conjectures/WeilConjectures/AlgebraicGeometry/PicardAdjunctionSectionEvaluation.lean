/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Evaluation of a pullback adjunction on the unit section

Source: Stacks Project, Tags 08HY and 0D5S; the unit formula for adjunctions.
(blueprint: lem-sc-picard-adjunction-section-evaluation)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Evaluation of the transpose of a unit morphism agrees with restriction to top.
Source: Stacks Project, Tags 08HY and 0D5S; the adjunction unit formula.
(blueprint: lem-sc-picard-adjunction-section-evaluation)
Proof: By right naturality of the Hom equivalence, the transpose of e followed by n
is the structure-sheaf map followed by pushforward of n. The structure-sheaf map
preserves 1. Naturality of n for the inclusion of top into the inverse image of top
then identifies the restriction of that value with n(1) on top. -/
theorem picardAdjunctionSectionEvaluation
    {Y Z : Scheme.{v}} (p : Z ⟶ Y) (F : Y.Modules ⥤ Z.Modules)
    (adj : F ⊣ Modules.pushforward p)
    (e : F.obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit Z.ringCatSheaf)
    (he : adj.homEquiv _ _ e.hom =
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom)
    (N : Z.Modules) (n : SheafOfModules.unit Z.ringCatSheaf ⟶ N) :
    N.presheaf.map (homOfLE p.preimage_top.ge).op
      ((adj.homEquiv _ _ (e.hom ≫ n)).val.app (Opposite.op ⊤) (1 : Γ(Y, ⊤))) =
        n.val.app (Opposite.op ⊤) (1 : Γ(Z, ⊤)) := by
  rw [adj.homEquiv_naturality_right, he]
  change N.presheaf.map _
    (n.val.app _ (p.toRingCatSheafHom.hom.app _ (1 : Γ(Y, ⊤)))) = _
  rw [map_one]
  simp

end AlgebraicGeometry.Scheme
