/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
/-! # The two tensor action maps

Construction part of the tensor change-of-rings presentation.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
-- Lift a natural bilinear pairing on sections through tensor sheafification.
open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_tensor_pairing {Y : Scheme.{u}} (M N Q : Y.Modules)
    (f : ∀ W : Y.Opens, M.val.obj (op W) → N.val.obj (op W) → Q.val.obj (op W))
    (hadd₁ : ∀ W x x' y, f W (x + x') y = f W x y + f W x' y)
    (hsmul₁ : ∀ W (r : Y.presheaf.obj (op W)) x y,
      f W (r • x) y = r • f W x y)
    (hadd₂ : ∀ W x y y', f W x (y + y') = f W x y + f W x y')
    (hsmul₂ : ∀ W (r : Y.presheaf.obj (op W)) x y,
      f W x (r • y) = r • f W x y)
    (hnat : ∀ (U V : Y.Opens) (i : V ⟶ U) x y,
      Q.val.map i.op (f U x y) = f V (M.val.map i.op x) (N.val.map i.op y)) :
    ∃ e : M ⊗ N ⟶ Q, ∀ W x y, e.app W (tmulSection x y) = f W x y := by
  let g : M.val ⊗ N.val ⟶ Q.val :=
    { app := fun W ↦ ModuleCat.MonoidalCategory.tensorLift (f W.unop)
        (hadd₁ W.unop) (hsmul₁ W.unop) (hadd₂ W.unop) (hsmul₂ W.unop)
      naturality := by
        intro U V i
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        exact (hnat U.unop V.unop i.unop x y).symm }
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Y.ringCatSheaf.obj)
  let e : sheafifyTensor M N ⟶ Q := (adj.homEquiv (M.val ⊗ N.val) Q).symm g
  refine ⟨(SheafOfModules.tensorObjIsoSheafification M N).hom ≫ e, ?_⟩
  intro W x y
  have h := (adj.homEquiv (M.val ⊗ N.val) Q).apply_symm_apply g
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun k ↦ k.app (op W) (x ⊗ₜ[Y.presheaf.obj (op W)] y)) h
  change Hom.app e W (Hom.app (SheafOfModules.tensorObjIsoSheafification M N).hom W
    (Hom.app (SheafOfModules.tensorObjIsoSheafification M N).inv W
      ((toSheafifyTensor M N).app (op W) (x ⊗ₜ y)))) = _
  exact (congrArg (Hom.app e W)
    (inv_app_hom_app_apply_of_iso (SheafOfModules.tensorObjIsoSheafification M N).symm
      ((toSheafifyTensor M N).app (op W) (x ⊗ₜ y)))).trans hh

set_option backward.isDefEq.respectTransparency false in
/-- The two action maps exist with their section formulas.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
(blueprint: lem-weil-pbc-change-of-rings-tensor-action-maps-actions).

Proof: put P₀ = P restricted to O_Y and K = C.toModule.val tensor P₀.val.
Give K the two B-actions b(c tensor p) = c tensor bp and
b(c tensor p) = phi(b)c tensor p. The first respects O_Y-balancing by
commutativity of B and the scalar-tower identity; the second respects it
because phi is an O_Y-algebra morphism. Restrictions commute with each
action by naturality of phi and semilinearity of the module restrictions.
Sheafify each B-module presheaf. After restriction to O_Y both associated
module sheaves identify with the O_Y-sheafification of K: the underlying
additive sheafification is the same and the O_Y-action is uniquely determined
by its restriction to the sheafification unit. Transport the B-actions
through these identifications to S = C.toModule tensor P₀. Their pairings
B.toModule.val times S.val are O_Y-bilinear and natural. Apply the sectionwise
tensor universal property and then the sheafification adjunction to obtain
a and d. The identifications preserve the units, so on the indicated double
pure tensors their values are c tensor bp and phi(b)c tensor p. The universal
properties apply to empty opens and zero modules without extra hypotheses.
-/
theorem exists_changeOfRings_tensor_action_maps_actions (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    ∃ (a d : tensorObj B.toModule (tensorObj C.toModule
      ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)) ⟶
      tensorObj C.toModule ((SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
        (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        a.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
          tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c (b • p)) ∧
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
        (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        d.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P) c p)) =
          tmulSection (M := C.toModule)
            (N := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P)
            (φ.right.hom.app (op W) b * c) p) := by
  let B₀ : Y.Modules := B.toModule
  let C₀ : Y.Modules := C.toModule
  let P₀ : Y.Modules := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
  obtain ⟨act, hact⟩ := exists_tensor_pairing B₀ P₀ P₀
    (fun W b p ↦ (show B.right.obj.obj (op W) from b) •
      (show P.val.obj (op W) from p))
    (by
      intro W b b' p
      change B.right.obj.obj (op W) at b b'
      change P.val.obj (op W) at p
      exact add_smul b b' p)
    (by
      intro W r b p
      change B.right.obj.obj (op W) at b
      change P.val.obj (op W) at p
      change (B.hom.hom.app (op W) r * b) • p = B.hom.hom.app (op W) r • (b • p)
      exact mul_smul _ _ _)
    (by
      intro W b p p'
      change B.right.obj.obj (op W) at b
      change P.val.obj (op W) at p p'
      exact smul_add b p p')
    (by
      intro W r b p
      change B.right.obj.obj (op W) at b
      change P.val.obj (op W) at p
      change b • (B.hom.hom.app (op W) r • p) = B.hom.hom.app (op W) r • (b • p)
      exact smul_comm _ _ _)
    (by
      intro U V i b p
      exact P.val.map_smul i.op b p)
  obtain ⟨mul, hmul⟩ := exists_tensor_pairing B₀ C₀ C₀
    (fun W b c ↦ φ.right.hom.app (op W) b *
      (show C.right.obj.obj (op W) from c))
    (by
      intro W b b' c
      change B.right.obj.obj (op W) at b b'
      change C.right.obj.obj (op W) at c
      simp only [map_add, add_mul])
    (by
      intro W r b c
      change B.right.obj.obj (op W) at b
      change C.right.obj.obj (op W) at c
      change φ.right.hom.app (op W) (B.hom.hom.app (op W) r * b) * c =
        C.hom.hom.app (op W) r * (φ.right.hom.app (op W) b * c)
      rw [map_mul]
      have hφ := ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.hom.app (op W)) (Under.w φ)) r
      change φ.right.hom.app (op W) (B.hom.hom.app (op W) r) =
        C.hom.hom.app (op W) r at hφ
      exact (congrArg (fun z ↦ z * φ.right.hom.app (op W) b * c) hφ).trans
        (mul_assoc _ _ _))
    (by
      intro W b c c'
      change C.right.obj.obj (op W) at c c'
      exact mul_add _ c c')
    (by
      intro W r b c
      change B.right.obj.obj (op W) at b
      change C.right.obj.obj (op W) at c
      change φ.right.hom.app (op W) b * (C.hom.hom.app (op W) r * c) =
        C.hom.hom.app (op W) r * (φ.right.hom.app (op W) b * c)
      exact mul_left_comm _ _ _)
    (by
      intro U V i b c
      change B.right.obj.obj (op U) at b
      change C.right.obj.obj (op U) at c
      change C.right.obj.map i.op (φ.right.hom.app (op U) b * c) = _
      rw [map_mul]
      have hn := ConcreteCategory.congr_hom (φ.right.hom.naturality i.op) b
      exact congrArg (· * C.right.obj.map i.op c) hn.symm)
  let a : tensorObj B₀ (tensorObj C₀ P₀) ⟶ tensorObj C₀ P₀ :=
    (MonoidalCategory.associator B₀ C₀ P₀).inv ≫
      (MonoidalCategory.whiskerRight (BraidedCategory.braiding B₀ C₀).hom P₀) ≫
      (MonoidalCategory.associator C₀ B₀ P₀).hom ≫ (MonoidalCategory.whiskerLeft C₀ act)
  let d : tensorObj B₀ (tensorObj C₀ P₀) ⟶ tensorObj C₀ P₀ :=
    (MonoidalCategory.associator B₀ C₀ P₀).inv ≫ (MonoidalCategory.whiskerRight mul P₀)
  refine ⟨a, d, ?_, ?_⟩
  · intro W b c p
    change Hom.app (MonoidalCategory.whiskerLeft C₀ act) W
      (Hom.app (MonoidalCategory.associator C₀ B₀ P₀).hom W
        (Hom.app (MonoidalCategory.whiskerRight (BraidedCategory.braiding B₀ C₀).hom P₀) W
          (Hom.app (MonoidalCategory.associator B₀ C₀ P₀).inv W
            (tmulSection (M := B₀) b (tmulSection (M := C₀) c p))))) = _
    have h₁ := associator_inv_app_tmulSection (M := B₀) (N := C₀) (P := P₀) b c p
    have h₂ := whiskerRight_app_tmulSection (N := P₀) (BraidedCategory.braiding B₀ C₀).hom
      (tmulSection (M := B₀) b c) p
    have h₃ := braiding_hom_app_tmulSection (M := B₀) (N := C₀) b c
    have h₄ := associator_hom_app_tmulSection (M := C₀) (N := B₀) (P := P₀) c b p
    have h₅ := whiskerLeft_app_tmulSection (M := C₀) act c (tmulSection (M := B₀) b p)
    rw [h₁, h₂, h₃, h₄, h₅, hact]
  · intro W b c p
    change Hom.app (MonoidalCategory.whiskerRight mul P₀) W
      (Hom.app (MonoidalCategory.associator B₀ C₀ P₀).inv W
        (tmulSection (M := B₀) b (tmulSection (M := C₀) c p))) = _
    have h₁ := associator_inv_app_tmulSection (M := B₀) (N := C₀) (P := P₀) b c p
    have h₂ := whiskerRight_app_tmulSection (N := P₀) mul (tmulSection (M := B₀) b c) p
    rw [h₁, h₂, hmul]
end AlgebraicGeometry.Scheme.Modules
