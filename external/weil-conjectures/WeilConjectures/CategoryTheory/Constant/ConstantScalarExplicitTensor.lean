/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-! # Constant scalar restriction for the explicit site tensor

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.ConstantScalarRestriction
attribute [local instance] Sheaf.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (B : Type (max u v)) [CommRing B]

/-- Restriction identifies constant scalars and the explicit sheafified site tensor
with the fixed-coefficient unit and tensor, preserving their local generators.
Source: Stacks 03CY and 03EK
(blueprint: lem-amb-constant-scalar-explicit-tensor).

Proof: take the inverse unit comparison of `ordinary J B` and identify its source
with the constant module sheaf. Its scalar equation is `Ordinary.unit_hom`, followed
by the inverse identity. For the tensor, compose the tensorator of `ordinary J B`
with restriction of the inverse monoidal presentation of the explicit site tensor.
The presheaf comparison between the two tensor presentations is the identity on
pure tensors. Naturality of the module sheafification unit therefore sends each
fixed pure tensor to the displayed site pure tensor. `Ordinary.tensor_inv` supplies
the first equation; the two sheafification adjunction triangles supply the second.
The inverse maps are the inverse tensorator and inverse presentation. These formulas
also hold for the zero ring and the empty site, with no flatness assumption. -/
theorem explicit_tensor_comparisons :
    ∃ e0 : (constantSheaf J (ModuleCat.{max u v} B)).obj (ModuleCat.of B B) ≅
      (restriction J B).obj (SheafOfModules.unit _),
    (∀ (U : Cᵒᵖ) (b : B), e0.hom.hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of B B))).app U b) =
        (realizationRingUnit J B).app U b) ∧
    ∀ M N : Modules J B,
      ∃ e : (restriction J B).obj M ⊗ (restriction J B).obj N ≅
        (restriction J B).obj ((SheafOfModules.siteSheafTensorRight N).obj M),
      ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
        e.hom.hom.app U
          ((Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{max u v} B))
            ((restriction J B).obj M) ((restriction J B).obj N)).app U (x ⊗ₜ[B] y)) =
          SheafOfModules.siteSheafTensorTmul M N U x y := by
  let m := ordinary J B
  let : (restriction J B).Monoidal := m.braided.toMonoidal
  let F := restriction J B
  refine ⟨(fixedUnitIso J B).symm ≪≫ Functor.Monoidal.εIso F, ?_, ?_⟩
  · intro U b
    apply (ModuleCat.mono_iff_injective
      ((Functor.OplaxMonoidal.η F).hom.app U)).mp inferInstance
    have hi := ConcreteCategory.congr_hom
      (congr_app (congrArg (fun q ↦ q.hom) (Functor.Monoidal.ε_η F)) U)
      ((fixedUnitIso J B).inv.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of B B))).app U b))
    change (Functor.OplaxMonoidal.η F).hom.app U
      ((Functor.LaxMonoidal.ε F).hom.app U _) = _ at hi
    exact hi.trans (m.unit_hom U b).symm
  · intro M N
    let a : PresheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (ring J B)).obj ⥤
        Modules J B := PresheafOfModules.sheafification (𝟙 _)
    let q : M.val ⊗ N.val ≅ SheafOfModules.siteTensorPresheaf M.val N.val :=
      PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by
        intro U V f
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        rfl)
    let e : M ⊗ N ≅ (SheafOfModules.siteSheafTensorRight N).obj M :=
      SheafOfModules.tensorObjIsoSheafification M N ≪≫ a.mapIso q
    refine ⟨Functor.Monoidal.μIso F M N ≪≫ F.mapIso e, ?_⟩
    intro U x y
    have hp := m.tensor_inv M N U x y
    change (Functor.LaxMonoidal.μ F M N).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{max u v} B))
        (F.obj M) (F.obj N)).app U (x ⊗ₜ[B] y)) = ringPure J B M N U x y at hp
    change (F.map e.hom).hom.app U
      ((Functor.LaxMonoidal.μ F M N).hom.app U _) = _
    rw [hp]
    change (a.map q.hom).val.app U
      ((SheafOfModules.tensorObjIsoSheafification M N).hom.val.app U
        ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U _)) = _
    have hi := congrArg (fun v ↦ v.val.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        (M.val ⊗ N.val)).app U (x ⊗ₜ[(ring J B).obj.obj U] y)))
      (SheafOfModules.tensorObjIsoSheafification M N).inv_hom_id
    change (SheafOfModules.tensorObjIsoSheafification M N).hom.val.app U
      ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U _) = _ at hi
    rw [hi]
    have hn := congrArg (fun v ↦ v.app U (x ⊗ₜ[(ring J B).obj.obj U] y))
      ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.naturality q.hom)
    exact hn.symm

end CategoryTheory.ConstantScalarRestriction
