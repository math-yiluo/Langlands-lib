/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # The degree-zero cup-product morphism

Source: Stacks Project, Tag 0BDP, final paragraph.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The unique comparison of the tensor-formula pullback with ordinary pullback.
Source: Stacks Project, Tags 0095 and 0096; uniqueness of left adjoints.
(blueprint: def-sc-picard-cup-product-map) -/
noncomputable def picardTensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) :
    tensorPullback p ≅ pullback p :=
  (Classical.choose (exists_tensorPullbackAdjunction p)).leftAdjointUniq
    (pullbackPushforwardAdjunction p)

/-- The tensor comparison for the tensor-formula pullback, transported from ordinary
pullback. Source: Stacks Project, Tag 0095, tensor formula.
(blueprint: def-sc-picard-cup-product-map) -/
noncomputable def picardTensorObjIso {X Y : Scheme.{u}} (p : X ⟶ Y) (M N : Y.Modules) :
    (tensorPullback p).obj (M ⊗ N) ≅
      (tensorPullback p).obj M ⊗ (tensorPullback p).obj N :=
  (picardTensorComparison p).app (M ⊗ N) ≪≫
    (Functor.Monoidal.μIso (pullback p) M N).symm ≪≫
      (((picardTensorComparison p).app M).symm ⊗ᵢ
        ((picardTensorComparison p).app N).symm)

/-- The unit comparison for tensor pullback.
Source: Stacks Project, Tag 0095, tensor formula.
(blueprint: def-sc-picard-cup-product-map) -/
noncomputable def picardTensorUnitIso {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (tensorPullback p).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (picardTensorComparison p).app _ ≪≫ pullbackObjUnitIso p

/-- Push a pairing forward, using the inverse of the structure-sheaf unit.
All maps are constructed from evaluation, the tensor comparison, and adjunction.
Source: Stacks Project, Tag 0BDP, degree-zero cup product.
(blueprint: def-sc-picard-cup-product-map) -/
noncomputable def picardPushforwardPairing {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hO : IsIso ((Classical.choose (exists_tensorPullbackAdjunction p)).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)))
    (M N : X.Modules) (ev : M ⊗ N ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (pushforward p).obj M ⊗ (pushforward p).obj N ⟶
      SheafOfModules.unit Y.ringCatSheaf := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction p)
  letI : IsIso (adj.unit.app (SheafOfModules.unit Y.ringCatSheaf)) := hO
  exact adj.homEquiv _ _
    ((picardTensorObjIso p _ _).hom ≫
      (adj.counit.app M ⊗ₘ adj.counit.app N) ≫ ev) ≫
    (pushforward p).map (picardTensorUnitIso p).inv ≫
      inv (adj.unit.app (SheafOfModules.unit Y.ringCatSheaf))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pulling cup product back recovers evaluation of the two counits.
Source: Stacks Project, Tag 0BDP, products of the dual basis sections.
(blueprint: def-sc-picard-cup-product-map) -/
theorem picardPushforwardPairing_counit {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hO : IsIso ((Classical.choose (exists_tensorPullbackAdjunction p)).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)))
    (M N : X.Modules) (ev : M ⊗ N ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (tensorPullback p).map (picardPushforwardPairing p hO M N ev) ≫
        (picardTensorUnitIso p).hom =
      (picardTensorObjIso p _ _).hom ≫
        ((Classical.choose (exists_tensorPullbackAdjunction p)).counit.app M ⊗ₘ
          (Classical.choose (exists_tensorPullbackAdjunction p)).counit.app N) ≫ ev := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction p)
  have : IsIso (adj.unit.app (SheafOfModules.unit Y.ringCatSheaf)) := hO
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]
  rw [Functor.map_comp, ← Category.assoc, adj.unit_naturality]
  simp only [Category.assoc]
  unfold picardPushforwardPairing
  dsimp only [adj]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp,
    Iso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- The transpose of the pushed-forward evaluation of E and its dual on X_W.
This is an actual construction, requiring no finite-free frame or existence theorem
for the desired morphism. Source: Stacks Project, Tag 0BDP, final paragraph.
(blueprint: def-sc-picard-cup-product-map) -/
noncomputable def picardCupProductMap {X S W : Scheme.{u}} (f : X ⟶ S)
    (E : X.Modules) (j : W ⟶ S)
    (hO : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).unit.app
        (SheafOfModules.unit W.ringCatSheaf))) :
    ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E))) ⟶
    Modules.dual ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj E)) :=
  let q := pullback.fst f j
  MonoidalClosed.curry (Modules.picardPushforwardPairing (pullback.snd f j) hO
    ((Modules.tensorPullback q).obj E) ((Modules.tensorPullback q).obj (Modules.dual E))
    ((Modules.picardTensorObjIso q E (Modules.dual E)).inv ≫
      (Modules.tensorPullback q).map (Modules.dualEvaluation E) ≫
        (Modules.picardTensorUnitIso q).hom))

end AlgebraicGeometry.Scheme
