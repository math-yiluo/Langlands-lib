/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeRestrictedLiftSectionsCore

/-! # Augmentation of the restricted lift

Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
(blueprint: lem-weil-pbc-restricted-lift-augmentation).
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

-- The nested restriction-adjunction calculation needs elaboration fuel.
/-- The explicitly restricted lift preserves the augmentation.
Source: Stacks Project, Cohomology, Tags 01FB and 01E4.
(blueprint: lem-weil-pbc-restricted-lift-augmentation).
Proof: Take the degree-zero component of the restriction adjunction defining
flatBaseChangeRestrictedLift. Use naturality of each composition/congruence
comparison to move the target augmentation through it. The target comparison's
augmentation cancels its inverse. Substitute ht. The unit square in D identifies
the resulting composite with the adjoint of D.psi followed by the target
augmentation. The source comparison's augmentation identifies the restricted
source augmentation; the bijection of the restriction adjunction then gives the
claimed equality. This argument needs no injectivity or flatness. -/
theorem flatBaseChangeRestrictedLift_augmentation {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S)
    {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex)
    (ht : I.ι.f 0 ≫ t.f 0 =
      (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F ≫
        (pushforward (pullback.snd g f)).map (J.ι.f 0))
    (V : S.Opens) (D : FlatBaseChangeOpenChoices f g F I J V) :
    let h := (pullback.snd g f).resLE (f ⁻¹ᵁ V)
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl
    D.source.resolution.ι.f 0 ≫ (flatBaseChangeRestrictedLift f g I J t V D).f 0 =
      D.psi ≫ (pushforward h).map (D.target.resolution.ι.f 0) := by
  let U := f ⁻¹ᵁ V
  let W := (pullback.snd g f) ⁻¹ᵁ U
  let h := (pullback.snd g f).resLE U W le_rfl
  let R := restrictFunctor U.ι
  let P := pushforward U.ι
  let H := pushforward h
  let G := pushforward (pullback.snd g f)
  let C := restrictFunctor W.ι
  let adj := restrictAdjunction U.ι
  let e₁ := pushforwardComp W.ι (pullback.snd g f)
  let e₂ := pushforwardCongr
    ((pullback.snd g f).resLE_comp_ι (U := U) (V := W) le_rfl)
  let e₃ := pushforwardComp h U.ι
  let F' := (tensorPullback (pullback.snd g f)).obj F
  let u := (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd g f))).unit.app F
  let w := (restrictAdjunction W.ι).unit
  have hu : u ≫ G.map (w.app F') ≫ e₁.hom.app (C.obj F') ≫
      e₂.inv.app (C.obj F') ≫ e₃.inv.app (C.obj F') =
        adj.unit.app F ≫ P.map D.psi := by
    have hs := congrArg (fun z ↦ z ≫ e₂.inv.app (C.obj F') ≫
      e₃.inv.app (C.obj F')) D.unit_square.symm
    change (u ≫ G.map (w.app F') ≫ e₁.hom.app (C.obj F')) ≫
      e₂.inv.app (C.obj F') ≫ e₃.inv.app (C.obj F') =
      (adj.unit.app F ≫ P.map D.psi ≫ e₃.hom.app (C.obj F') ≫
        e₂.hom.app (C.obj F')) ≫ e₂.inv.app (C.obj F') ≫ e₃.inv.app (C.obj F') at hs
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
      Functor.comp_obj] at hs
    exact hs.trans (Category.comp_id (adj.unit.app F ≫ P.map D.psi))
  let δ : G ⟶ C ⋙ H ⋙ P :=
    (Functor.leftUnitor G).inv ≫
      Functor.whiskerRight w G ≫ (Functor.associator C (pushforward W.ι) G).hom ≫
        Functor.whiskerLeft C e₁.hom ≫ Functor.whiskerLeft C e₂.inv ≫ Functor.whiskerLeft C e₃.inv
  have hδ : u ≫ δ.app F' = adj.unit.app F ≫ P.map D.psi := by
    dsimp only [δ, NatTrans.comp_app, Functor.whiskerRight, Functor.whiskerLeft,
      Functor.leftUnitor, Functor.associator]
    simp only [Functor.comp_obj, Category.id_comp]
    erw [Category.id_comp]
    exact hu
  let i : F ⟶ I.cocomplex.X 0 := I.ι.f 0
  let j : F' ⟶ J.cocomplex.X 0 := J.ι.f 0
  let a : C.obj F' ⟶ D.target.resolution.cocomplex.X 0 := D.target.resolution.ι.f 0
  have htar : C.map j ≫ D.target.comparison.inv.f 0 = a := by
    change (restrictFunctor W.ι).map (J.ι.f 0) ≫ D.target.comparison.inv.f 0 = _
    rw [← D.target.augmentation, Category.assoc]
    simp only [← HomologicalComplex.comp_f, Iso.hom_inv_id,
      HomologicalComplex.id_f, Category.comp_id]
    rfl
  let b : I.cocomplex.X 0 ⟶ P.obj (H.obj (D.target.resolution.cocomplex.X 0)) :=
    t.f 0 ≫ δ.app (J.cocomplex.X 0) ≫ P.map (H.map (D.target.comparison.inv.f 0))
  have hb : i ≫ b = adj.unit.app F ≫ P.map (D.psi ≫ H.map a) := by
    dsimp only [b]
    rw [← Category.assoc]
    change (I.ι.f 0 ≫ t.f 0) ≫ _ = _
    rw [ht]
    change (u ≫ G.map j) ≫ δ.app (J.cocomplex.X 0) ≫
      P.map (H.map (D.target.comparison.inv.f 0)) = _
    rw [Category.assoc, δ.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← P.map_comp, ← H.map_comp, htar, ← Category.assoc, hδ, Category.assoc,
      ← P.map_comp]
  change D.source.resolution.ι.f 0 ≫ D.source.comparison.hom.f 0 ≫
    (adj.homEquiv _ _).symm b = _
  rw [← Category.assoc, D.source.augmentation]
  change R.map (I.ι.f 0) ≫ (adj.homEquiv _ _).symm b = _
  rw [← adj.homEquiv_naturality_left_symm, hb]
  exact (adj.homEquiv F (H.obj (D.target.resolution.cocomplex.X 0))).symm_apply_apply
    (D.psi ≫ H.map (D.target.resolution.ι.f 0))


end AlgebraicGeometry.Scheme.Modules
