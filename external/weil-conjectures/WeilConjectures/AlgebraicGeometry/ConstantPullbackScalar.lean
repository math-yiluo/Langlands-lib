/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantInverseImageSection
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction

/-! # Constant scalar multiplication under module inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D7;
Cohomology on Sites, Tag 093M (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ConstantCompletion

open SheafOfModules

private theorem change_scalar
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S)
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (b : (S.obj ⋙ forget CommRingCat).sections)
    (h : ∀ U, c.hom.app U (a.val U) = b.val U) (M : Mod R) :
    (change c).map ⟨PresheafOfModules.sectionsSMul M.val a⟩ =
      ⟨PresheafOfModules.sectionsSMul ((change c).obj M).val b⟩ := by
  apply ((tensorAdjunction c).homEquiv M ((change c).obj M)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hn := (tensorAdjunction c).unit.naturality
    (show M ⟶ M from ⟨PresheafOfModules.sectionsSMul M.val a⟩)
  change (show M ⟶ M from ⟨PresheafOfModules.sectionsSMul M.val a⟩) ≫
      (tensorAdjunction c).unit.app M =
    (tensorAdjunction c).unit.app M ≫
      (restriction c).map ((change c).map ⟨PresheafOfModules.sectionsSMul M.val a⟩) at hn
  rw [← hn]
  apply SheafOfModules.hom_ext
  ext U x
  change ((tensorAdjunction c).unit.app M).val.app U (a.val U • x) =
    b.val U • (show ((change c).obj M).val.obj U from
      ((tensorAdjunction c).unit.app M).val.app U x)
  rw [map_smul]
  change c.hom.app U (a.val U) •
      (show ((change c).obj M).val.obj U from
        ((tensorAdjunction c).unit.app M).val.app U x) =
    b.val U • (show ((change c).obj M).val.obj U from
      ((tensorAdjunction c).unit.app M).val.app U x)
  rw [h]

/-- Constant-coefficient pullback carries scalar multiplication to its transported section.

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D7;
Cohomology on Sites, Tag 093M (auxiliary; not a blueprint node).

Proof: inverseImageSection_map identifies the scalar on every test sheaf. Apply
moduleSMul to the underlying sheaf of M, the scalar map, the identity and scalar
multiplication. Naturality of moduleUnderlying gives the algebraic inverse-image
endomorphism. The scalar-extension adjunction unit is linear, and its naturality
identifies the image after scalar extension with multiplication by the structural
image of the transported section. -/
theorem constantPullback_scalar
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    (A : Type u) [CommRing A]
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)}
    [PreservesFiniteLimits L] (F : InverseImageData L)
    (a : A) (M : Mod (constant JC A)) :
    (pull F (constantMap F A)).map
        ⟨PresheafOfModules.sectionsSMul M.val (constantSection (J := JC) a)⟩ =
      ⟨PresheafOfModules.sectionsSMul
        ((pull F (constantMap F A)).obj M).val (transportedConstantSection F A a)⟩ := by
  let b := inverseImageSection F (constant JC A) (constantSection (J := JC) a)
  have hb (U : Eᵒᵖ) : (constantMap F A).hom.app U (b.val U) =
      (transportedConstantSection F A a).val U := rfl
  let AI := F.algebra (constant JC A)
  let μ : M ⟶ M := ⟨PresheafOfModules.sectionsSMul M.val (constantSection (J := JC) a)⟩
  have hi : AI.modules.map μ =
      ⟨PresheafOfModules.sectionsSMul (AI.modules.obj M).val b⟩ := by
    apply (underlying (F.rings.obj (constant JC A))).map_injective
    apply (cancel_epi (AI.moduleUnderlying.inv.app M)).mp
    have hn := AI.moduleUnderlying.inv.naturality μ
    change L.map ((underlying (constant JC A)).map μ) ≫ AI.moduleUnderlying.inv.app M =
      AI.moduleUnderlying.inv.app M ≫
        (underlying (F.rings.obj (constant JC A))).map (AI.modules.map μ) at hn
    rw [← hn]
    ext U x
    have hsm := AI.moduleSMul M ((underlying (constant JC A)).obj M)
      (constantSectionMap A a _) (𝟙 _) ((underlying (constant JC A)).map μ)
      (fun _ _ ↦ rfl) U x
    have hx : AI.ringUnderlying.hom.hom.app U
        ((L.map (constantSectionMap A a ((underlying (constant JC A)).obj M))).hom.app U x) =
      b.val U := congrArg (fun f ↦ f.hom.app U x)
        (inverseImageSection_map F (constant JC A) (constantSection (J := JC) a)
          ((underlying (constant JC A)).obj M))
    change (AI.moduleUnderlying.inv.app M).hom.app U
        ((L.map ((underlying (constant JC A)).map μ)).hom.app U x) =
      b.val U • (show (AI.modules.obj M).val.obj U from
        (AI.moduleUnderlying.inv.app M).hom.app U x)
    simp only [Functor.map_id] at hsm
    change (AI.moduleUnderlying.inv.app M).hom.app U
        ((L.map ((underlying (constant JC A)).map μ)).hom.app U x) =
      (show (F.rings.obj (constant JC A)).obj.obj U from
        AI.ringUnderlying.hom.hom.app U
          ((L.map (constantSectionMap A a ((underlying (constant JC A)).obj M))).hom.app U x)) •
        (show (AI.modules.obj M).val.obj U from
          (AI.moduleUnderlying.inv.app M).hom.app U x) at hsm
    rw [hx] at hsm
    exact hsm
  change (change (constantMap F A)).map (AI.modules.map μ) = _
  rw [hi]
  exact change_scalar (constantMap F A) b (transportedConstantSection F A a) hb
    (AI.modules.obj M)

end CategoryTheory.ConstantCompletion
