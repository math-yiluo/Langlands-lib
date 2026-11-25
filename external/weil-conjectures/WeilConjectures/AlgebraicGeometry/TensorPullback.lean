/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Pullback of scheme modules by the tensor formula

Source: Stacks Project, Tags 0095, 0096, 0097; blueprint module base change in
`sec-abelian-varieties/def-sc-jacobian/def-pc-base-change.md`
(blueprint: def-pc-module-pullback).
-/

@[expose] public section

universe w

open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Z : Scheme.{w}} (g : X ⟶ Y)

/-- The ring map `g⁻¹ O_Y → O_X` adjoint to the structure-sheaf map of `g`.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
def tensorPullbackRingMap : TopCat.Sheaf.inverseImageRing g.base Y.sheaf ⟶ X.sheaf := by
  have : ∀ (F : (Opens Y)ᵒᵖ ⥤ CommRingCat.{w}),
      (Opens.map g.base).op.HasLeftKanExtension F := fun F ↦ by
    have : (Opens.map g.base).op.HasPointwiseLeftKanExtension F := fun _ ↦ inferInstance
    exact Functor.HasLeftKanExtension.mk _
      (Functor.pointwiseLeftKanExtensionUnit (Opens.map g.base).op F)
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map g.base) CommRingCat.{w} _ _).homEquiv Y.sheaf X.sheaf |>.symm ⟨g.c⟩

/-- `O_X ⊗_{g⁻¹ O_Y} g⁻¹ M`: change of rings on the explicit abelian inverse image.
The section tensor has `O_X` as its first factor and is then sheafified.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
def tensorPullbackObj (M : Y.Modules) : X.Modules :=
  SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap g)
    (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)

/-- The sectionwise map of tensor presheaves is natural.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback).
Proof: inverse image of `a` is linear and commutes with restriction (008X).
The map `id ⊗ g⁻¹a` therefore commutes with restrictions on pure tensors;
pure tensors generate each section tensor, giving the asserted naturality. -/
theorem tensorPullbackPresheafMap_naturality {M N : Y.Modules} (a : M ⟶ N)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
      (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)).map i ≫
      (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).map
        ((ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app V).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app V)) =
    ((ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
      ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app U)) ≫
      (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.base Y.sheaf N)).map i := by
  exact SheafOfModules.changeOfRingsHom_naturality (tensorPullbackRingMap g)
    (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)
    (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a) i

/-- The tensor formula on morphisms, followed by module sheafification.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
def tensorPullbackMap {M N : Y.Modules} (a : M ⟶ N) :
    tensorPullbackObj g M ⟶ tensorPullbackObj g N :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    { app := fun U ↦
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app U)
      naturality := tensorPullbackPresheafMap_naturality g a }

/-- Tensor pullback preserves identities. Source: Stacks, Tag 0095
(blueprint: def-pc-module-pullback).
Proof: the abelian inverse-image functor preserves identities; its module map is the
same map with linearity supplied. Extension of scalars and sheafification preserve identities. -/
theorem tensorPullbackMap_id (M : Y.Modules) :
    tensorPullbackMap g (𝟙 M) = 𝟙 (tensorPullbackObj g M) := by
  let p :
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M) ⟶
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M) :=
    { app := fun U ↦
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M (𝟙 M)).val.app U)
      naturality := tensorPullbackPresheafMap_naturality g (𝟙 M) }
  have hp : p = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro U
    have hi :
        (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M (𝟙 M)).val.app U =
          𝟙 _ := by
      ext m
      simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
      rfl
    change (ModuleCat.extendScalars _).map _ = 𝟙 _
    rw [hi, CategoryTheory.Functor.map_id]
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map p = _
  rw [hp, CategoryTheory.Functor.map_id]
  rfl

/-- Tensor pullback preserves composition. Source: Stacks, Tag 0095
(blueprint: def-pc-module-pullback).
Proof: the abelian inverse-image functor preserves composition; its module map is the
same map with linearity supplied. Extension of scalars and sheafification preserve composition. -/
theorem tensorPullbackMap_comp {M N P : Y.Modules} (a : M ⟶ N) (b : N ⟶ P) :
    tensorPullbackMap g (a ≫ b) = tensorPullbackMap g a ≫ tensorPullbackMap g b := by
  unfold tensorPullbackMap
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  have hi :
      (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M (a ≫ b)).val.app U =
        (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app U ≫
          (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf N b).val.app U := by
    ext m
    simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
    rfl
  change (ModuleCat.extendScalars _).map _ =
    (ModuleCat.extendScalars _).map _ ≫ (ModuleCat.extendScalars _).map _
  rw [hi, CategoryTheory.Functor.map_comp]

/-- Pullback of modules along a scheme morphism, defined by the tensor formula.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
def tensorPullback : Y.Modules ⥤ X.Modules where
  obj := tensorPullbackObj g
  map := tensorPullbackMap g
  map_id := tensorPullbackMap_id g
  map_comp := tensorPullbackMap_comp g

private theorem tensorPullbackMap_toSheafify {M N : Y.Modules} (a : M ⟶ N)
    (U : (Opens X)ᵒᵖ)
    (t : (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
      (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)).obj U) :
    (tensorPullbackMap g a).val.app U
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
          (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)).presheaf).app U t) =
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.base Y.sheaf N)).presheaf).app U
      ((ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
        ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app U) t) := by
  let p :
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M) ⟶
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.base Y.sheaf N) :=
    { app := fun V ↦
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app V).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app V)
      naturality := tensorPullbackPresheafMap_naturality g a }
  exact congrArg (fun q ↦ q.app U t)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit_naturality p)

private abbrev tensorPullbackRingMapUnderlying :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{w} RingCat.{w})).map (tensorPullbackRingMap g)

private abbrev tensorPullbackRingUnit :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat.{w} RingCat.{w})).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map g.base) CommRingCat.{w} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app Y.sheaf)

private theorem tensorPullbackRingMap_unit :
    (tensorPullbackRingUnit g) ≫ ((Opens.map g.base).sheafPushforwardContinuous RingCat.{w}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map
        (tensorPullbackRingMapUnderlying g) =
      g.toRingCatSheafHom := by
  have ht := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map g.base) CommRingCat.{w} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology
      X)).homEquiv Y.sheaf X.sheaf
      |>.apply_symm_apply (show Y.sheaf ⟶
        ((Opens.map g.base).sheafPushforwardContinuous CommRingCat.{w}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
          X.sheaf from ⟨g.c⟩)
  rw [Adjunction.homEquiv_unit] at ht
  ext V r
  exact congrArg (fun t ↦ t.hom.app V r) ht

private def tensorPullbackPushforwardIso :
    SheafOfModules.restrictScalars (tensorPullbackRingMapUnderlying g) ⋙
      SheafOfModules.pushforward.{w} (tensorPullbackRingUnit g) ≅
      pushforward g :=
  (SheafOfModules.pushforwardComp (F := Opens.map g.base) (G := 𝟭 (Opens X))
    (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{w} RingCat.{w})).obj
        (TopCat.Sheaf.inverseImageRing g.base Y.sheaf))) (R' := X.ringCatSheaf) (S :=
          Y.ringCatSheaf) (tensorPullbackRingUnit g) (tensorPullbackRingMapUnderlying g)) ≪≫
    SheafOfModules.pushforwardCongr (tensorPullbackRingMap_unit g)

/-- The tensor formula is left adjoint to the sectionwise module pushforward.
Source: Stacks, Tag 0096 (blueprint: def-pc-module-pullback).
Proof: apply the tensor/restriction adjunction to the change of rings, then the
inverse-image/direct-image module adjunction (008Y). The resulting bijection is natural
and its right-hand module action is restriction along `g.c`, hence the recorded pushforward.
These are the first two steps of this node, using lem-pc-module-pullback-adjunction. -/
theorem nonempty_tensorPullbackAdjunction : Nonempty (tensorPullback g ⊣ pushforward g) := by
  obtain ⟨E, h, adj, he⟩ := SheafOfModules.exists_changeOfRingsAdjunction X.toTopCat
    (TopCat.Sheaf.inverseImageRing g.base Y.sheaf) X.sheaf (tensorPullbackRingMap g)
  obtain ⟨φ, hφ, _, _⟩ := SheafOfModules.moduleInverseImageAdjunction g.base Y.sheaf
  let e : ∀ (M : Y.Modules) (N : X.Modules),
      (tensorPullbackObj g M ⟶ N) ≃ (M ⟶ (pushforward g).obj N) := fun M N ↦
    ((Iso.homCongr (eqToIso (h (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M))).symm
      (Iso.refl N)).trans
      (adj.homEquiv (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M) N)).trans
      ((φ M ((SheafOfModules.restrictScalars (tensorPullbackRingMapUnderlying g)).obj N)).trans
        (Iso.homCongr (Iso.refl M) ((tensorPullbackPushforwardIso g).app N)))
  have eval (M : Y.Modules) (N : X.Modules) (a : tensorPullbackObj g M ⟶ N)
      (V : (Opens Y)ᵒᵖ) (m : M.val.obj V) :
      (e M N a).val.app V m =
        a.val.app ((Opens.map g.base).op.obj V)
          ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
              (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)).presheaf).app
            ((Opens.map g.base).op.obj V)
            ((1 : X.sheaf.obj.obj ((Opens.map g.base).op.obj V)) ⊗ₜ[
              (TopCat.Sheaf.inverseImageRing g.base Y.sheaf).obj.obj
                ((Opens.map g.base).op.obj V),
              ((tensorPullbackRingMap g).hom.app ((Opens.map g.base).op.obj V)).hom]
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (Opens.map g.base) AddCommGrpCat.{w} (Opens.grothendieckTopology Y)
                  (Opens.grothendieckTopology X)).unit.app
                  ((SheafOfModules.toSheaf _).obj M)).hom.app V m))) := by
    change (φ M ((SheafOfModules.restrictScalars (tensorPullbackRingMapUnderlying g)).obj N)
      ((adj.homEquiv _ _) (eqToHom (h _) ≫ a))).val.app V m = _
    rw [hφ]
    exact he _ _ a _ _
  have hl {M' M : Y.Modules} {N : X.Modules} (a : M' ⟶ M)
      (b : tensorPullbackObj g M ⟶ N) :
      e M' N (tensorPullbackMap g a ≫ b) = a ≫ e M N b := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext m
    let W := (Opens.map g.base).op.obj V
    let adjAb := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map g.base) AddCommGrpCat.{w} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)
    let x := ((adjAb.unit.app ((SheafOfModules.toSheaf _).obj M')).hom.app V m)
    have hn :
        (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M' a).val.app W x =
          (adjAb.unit.app ((SheafOfModules.toSheaf _).obj M)).hom.app V
            (a.val.app V m) := by
      exact congrArg (fun t ↦ t.hom.app V m)
        (adjAb.unit_naturality ((SheafOfModules.toSheaf _).map a))
    refine (eval M' N (tensorPullbackMap g a ≫ b) V m).trans ?_
    refine (congrArg (fun t ↦ b.val.app W t)
      (tensorPullbackMap_toSheafify g a W ((1 : X.sheaf.obj.obj W) ⊗ₜ[_, _] x))).trans ?_
    have ht :
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app W).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M' a).val.app W)
          ((1 : X.sheaf.obj.obj W) ⊗ₜ[_, _] x) =
        (1 : X.sheaf.obj.obj W) ⊗ₜ[_, ((tensorPullbackRingMap g).hom.app W).hom]
          (show (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M).val.obj W from
            (adjAb.unit.app ((SheafOfModules.toSheaf _).obj M)).hom.app V
              (a.val.app V m)) := by
      erw [ModuleCat.ExtendScalars.map_tmul]
      exact congrArg (fun y ↦ (1 : X.sheaf.obj.obj W) ⊗ₜ[_,
        ((tensorPullbackRingMap g).hom.app W).hom] y) hn
    exact (congrArg (fun t ↦ b.val.app W
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
          (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)).presheaf).app W t)) ht).trans
      (eval M N b V (a.val.app V m)).symm
  refine ⟨Adjunction.mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }⟩
  · intro M' M N a b
    apply (e M' N).injective
    exact (Equiv.apply_symm_apply (e M' N) (a ≫ b)).trans
      ((congrArg (fun t ↦ a ≫ t) (Equiv.apply_symm_apply (e M N) b)).symm.trans
        (hl a ((e M N).symm b)).symm)
  · intro M N N' a b
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext m
    exact (eval M N' (a ≫ b) V m).trans
      (congrArg (fun x ↦ b.val.app ((Opens.map g.base).op.obj V) x)
        (eval M N a V m).symm)

/-- Identity pullback is naturally isomorphic to the identity functor.
Source: Stacks, Tags 0095 and 0097 (blueprint: def-pc-module-pullback).
Proof: by the preceding adjunction and the identity pushforward isomorphism,
the tensor pullback of the identity and the identity functor are left adjoints of the
same functor. Uniqueness of left adjoints gives the isomorphism; this is the identity
case of step three, lem-pc-module-pullback-identity-composition. 
(blueprint: lem-pc-module-pullback-identity-composition)
-/
theorem nonempty_tensorPullbackId (T : Scheme.{w}) :
    Nonempty (tensorPullback (𝟙 T) ≅ 𝟭 T.Modules) := by
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction (𝟙 T)
  exact ⟨(adj.ofNatIsoRight (pushforwardId T)).leftAdjointUniq Adjunction.id⟩

/-- Composite pullback is naturally isomorphic to successive pullback.
Source: Stacks, Tag 0097 (blueprint: def-pc-module-pullback).
Proof: combine the two tensor-pullback adjunctions. Sectionwise pushforward composition
identifies their right adjoint with pushforward along `g ≫ h`. Uniqueness of left adjoints
gives this isomorphism; this is step three, lem-pc-module-pullback-identity-composition. 
(blueprint: lem-pc-module-pullback-identity-composition)
-/
theorem nonempty_tensorPullbackComp (h : Y ⟶ Z) :
    Nonempty (tensorPullback (g ≫ h) ≅ tensorPullback h ⋙ tensorPullback g) := by
  obtain ⟨adjg⟩ := nonempty_tensorPullbackAdjunction g
  obtain ⟨adjh⟩ := nonempty_tensorPullbackAdjunction h
  obtain ⟨adjgh⟩ := nonempty_tensorPullbackAdjunction (g ≫ h)
  exact ⟨adjgh.leftAdjointUniq ((adjh.comp adjg).ofNatIsoRight (pushforwardComp g h))⟩

end
end AlgebraicGeometry.Scheme.Modules
