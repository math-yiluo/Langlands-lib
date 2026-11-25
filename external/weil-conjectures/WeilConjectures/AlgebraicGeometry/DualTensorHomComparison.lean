/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic

/-! # Identifying the sheaf dual-tensor comparison with the categorical comparison

Source: Stacks Project, Modules, Example 0FNV, the canonical tensor-to-endomorphism map.
(blueprint: lem-ag-dual-tensor-hom-comparison)
-/

@[expose] public section

universe u

open CategoryTheory

section
universe v

open MonoidalCategory

section
variable {C : Type u} [Category C] [MonoidalCategory C]
  {D : Type v} [Category D] [MonoidalCategory D]
/-- A monoidal functor transports evaluation followed by scalar multiplication. -/
private theorem dualTensorHom_pairing (F : C ⥤ D) [F.Monoidal] (a b n : C) (A B N : D)
    (eA : F.obj a ≅ A) (eB : F.obj b ≅ B) (eN : F.obj n ≅ N)
    (eU : F.obj (𝟙_ C) ≅ 𝟙_ D) (hU : Functor.LaxMonoidal.ε F = eU.inv)
    (ev : a ⊗ b ⟶ 𝟙_ C) :
    A ◁ ((eB.inv ⊗ₘ eN.inv) ≫ Functor.LaxMonoidal.μ F b n) ≫
      eA.inv ▷ F.obj (b ⊗ n) ≫ Functor.LaxMonoidal.μ F a (b ⊗ n) ≫
      F.map ((α_ a b n).inv ≫ ev ▷ n ≫ (λ_ n).hom) ≫ eN.hom =
    (α_ A B N).inv ≫
      ((eA.inv ⊗ₘ eB.inv) ≫ Functor.LaxMonoidal.μ F a b ≫ F.map ev ≫ eU.hom) ▷ N ≫
        (λ_ N).hom := by
  simp only [Functor.map_comp, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [whisker_exchange_assoc, ← tensorHom_def'_assoc,
    Functor.LaxMonoidal.associativity_inv_assoc, associator_inv_naturality_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc]
  have hunit : Functor.LaxMonoidal.μ F (𝟙_ C) n ≫ F.map (λ_ n).hom =
      eU.hom ▷ F.obj n ≫ (λ_ (F.obj n)).hom := by
    rw [← cancel_epi (Functor.LaxMonoidal.ε F ▷ F.obj n),
      ← comp_whiskerRight_assoc, hU, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
    simpa only [hU] using (Functor.LaxMonoidal.left_unitality F n).symm
  have hunit' := hunit =≫ eN.hom
  simp only [Category.assoc] at hunit'
  rw [hunit', ← leftUnitor_naturality eN.hom]
  simp only [tensorHom_def, Category.assoc]
  rw [whisker_exchange_assoc, whisker_exchange_assoc, whisker_exchange_assoc,
    ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

end

namespace SheafOfModules
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{u} (𝟙 (𝓡).obj)
set_option hygiene false in
local notation "adj" => PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {R : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
attribute [local instance] monoidalCategory symmetricCategory monoidalClosed
-- Rewriting the localized monoidal structure requires unfolding its comparison functors.
set_option backward.isDefEq.respectTransparency false in
/-- Uncurrying a sheafified map is sheafification of its presheaf uncurry. -/
private theorem dualTensorHom_transport (A N : SheafOfModules.{u} 𝓡)
    (P : PresheafOfModules.{u} (𝓡).obj) (ψ : P ⟶ (homObj A N).val) :
    let := sheafificationMonoidal R
    MonoidalClosed.uncurry ((𝓢).map ψ ≫ (adj).counit.app (homObj A N)) =
      (asIso (adj).counit).inv.app A ▷ (𝓢).obj P ≫
        Functor.LaxMonoidal.μ (𝓢) A.val P ≫
        (𝓢).map (PresheafOfModules.tensorHomUncurry (R := R.obj) ψ) ≫
        (adj).counit.app N := by
  let := sheafificationMonoidal R
  let g : (𝓢).obj P ⟶ homObj A N := (𝓢).map ψ ≫ (adj).counit.app (homObj A N)
  have hψ : (adj).unit.app P ≫ g.val = ψ := by
    change (adj).homEquiv P (homObj A N) g = ψ
    change (adj).homEquiv P (homObj A N)
      (((adj).homEquiv P (homObj A N)).symm ψ) = ψ
    exact Equiv.apply_symm_apply _ _
  have hη : (𝓢).map ((adj).unit.app P) =
      (asIso (adj).counit).inv.app ((𝓢).obj P) := by
    rw [← cancel_mono ((adj).counit.app ((𝓢).obj P))]
    erw [Iso.inv_hom_id_app]
    exact (adj).left_triangle_components P
  have hunc : PresheafOfModules.tensorHomUncurry (R := R.obj) ψ =
      A.val ◁ (adj).unit.app P ≫
        PresheafOfModules.tensorHomUncurry (R := R.obj) g.val := by
    apply (PresheafOfModules.homObjEquiv (R := R.obj) _ _ _).injective
    rw [PresheafOfModules.homObjEquiv_whiskerLeft_comp]
    change (PresheafOfModules.homObjEquiv (R := R.obj) _ _ _)
      ((PresheafOfModules.homObjEquiv (R := R.obj) _ _ _).symm ψ) =
      (adj).unit.app P ≫
        (PresheafOfModules.homObjEquiv (R := R.obj) _ _ _)
          ((PresheafOfModules.homObjEquiv (R := R.obj) _ _ _).symm g.val)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hψ]
  rw [uncurry_eq_tensorHomEquiv_symm]
  change (tensorObjIsoSheafification A ((𝓢).obj P)).hom ≫
    ((adj).homEquiv _ N).symm
      (PresheafOfModules.tensorHomUncurry (R := R.obj) g.val) = _
  rw [Adjunction.homEquiv_counit, hunc, Functor.map_comp]
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    tensorIso_inv, Iso.app_inv, Functor.Monoidal.μIso_hom, Category.assoc]
  erw [← Functor.LaxMonoidal.μ_natural_right_assoc (𝓢) A.val ((adj).unit.app P), hη]
  rw [tensorHom_def_assoc]
  rfl
-- Rewriting the localized monoidal structure requires unfolding its comparison functors.
set_option backward.isDefEq.respectTransparency false in
/-- The two comparisons agree for sheaves of modules on any site. -/
private theorem dualTensorHom_comparison (A N : SheafOfModules.{u} 𝓡) :
    (tensorObjIsoSheafification (homObj A (unit 𝓡)) N).hom ≫
      (𝓢).map (PresheafOfModules.dualTensorHom A.val N.val) ≫
      (adj).counit.app (homObj A N) = MonoidalClosed.ihomUnitTensorToIhom A N := by
  let := sheafificationMonoidal R
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.ihomUnitTensorToIhom, MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_natural_left, dualTensorHom_transport]
  rw [PresheafOfModules.dualTensorHom]
  change _ ≫ _ ≫ _ ≫ (𝓢).map
    ((PresheafOfModules.homObjEquiv _ _ _).symm
      ((PresheafOfModules.homObjEquiv _ _ _) _)) ≫ _ = _
  rw [Equiv.symm_apply_apply]
  have hev : (ihom.ev A).app (unit 𝓡) =
      (tensorObjIsoSheafification A (homObj A (unit 𝓡))).hom ≫
      (𝓢).map (PresheafOfModules.tensorHomUncurry
        (R := R.obj) (𝟙 (homObj A (unit 𝓡)).val)) ≫ (adj).counit.app (unit 𝓡) := by
    rw [ihom_ev_app]
    change _ ≫ ((adj).homEquiv _ _).symm _ = _
    rw [Adjunction.homEquiv_counit]
    rfl
  erw [hev]
  exact dualTensorHom_pairing (𝓢) A.val (homObj A (unit 𝓡)).val N.val A
    (homObj A (unit 𝓡)) N ((asIso (adj).counit).app A)
    ((asIso (adj).counit).app (homObj A (unit 𝓡)))
    ((asIso (adj).counit).app N) ((asIso (adj).counit).app (unit 𝓡)) rfl
    (PresheafOfModules.tensorHomUncurry (R := R.obj) (𝟙 (homObj A (unit 𝓡)).val))
end SheafOfModules

end

namespace AlgebraicGeometry.Scheme.Modules

/-- The sheafified dual-tensor-to-Hom map is the canonical closed-category comparison.

Source: Stacks Project, Modules, Example 0FNV, canonical tensor-to-endomorphism map;
the two maps here are its natural generalization with arbitrary target `N`.

Proof: transpose both maps under the tensor-Hom adjunction. The categorical comparison
transposes, by definition, to associativity followed by evaluation of `M` against its
dual and multiplication of the resulting scalar on `N`. The sheaf comparison is the
sheafification of the presheaf map sending `phi tensor n` to `m ↦ phi(m) n`.
By the construction of the sheaf tensor-Hom adjunction through sheafification,
its transpose is the sheafification of that same evaluation-and-multiplication map.
On any open and any pure tensor `m tensor (phi tensor n)`, both presheaf maps send
this to `phi(m) n`. Tensor induction proves equality on all sections. Sheafification
preserves this equality, and naturality of its tensor and unit comparisons identifies
the endpoints. Injectivity of transposition gives the stated equality. No local
freeness assumption is needed.

(blueprint: lem-ag-dual-tensor-hom-comparison) -/
theorem dualTensorHom_eq_ihomUnitTensorToIhom {X : Scheme.{u}} (M N : X.Modules) :
    dualTensorHom M N = MonoidalClosed.ihomUnitTensorToIhom M N := by
  exact SheafOfModules.dualTensorHom_comparison (R := X.sheaf) M N

end AlgebraicGeometry.Scheme.Modules
