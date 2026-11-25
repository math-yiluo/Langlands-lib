/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Concrete tensor pullback on modules of a ringed space

Source: Stacks Project, Tags 008A and 008Y.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

noncomputable section

open TopologicalSpace Opposite
open scoped ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : RingedSpace.{u}} (g : X ⟶ Y)

/-- The ring map `g⁻¹ O_Y → O_X` adjoint to the structure-sheaf map of `g`.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
private abbrev tensorPullbackRingMap :=
  CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩

private def tensorPullbackObj (M : (SheafOfModules.{u} (moduleRings Y))) : (SheafOfModules.{u}
  (moduleRings X)) :=
  SheafOfModules.changeOfRings.{u, u, u} (tensorPullbackRingMap g)
    (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)

/-- The sectionwise map of tensor presheaves is natural.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback).
Proof: inverse image of `a` is linear and commutes with restriction (008X).
The map `id ⊗ g⁻¹a` therefore commutes with restrictions on pure tensors;
pure tensors generate each section tensor, giving the asserted naturality. -/
private theorem tensorPullbackPresheafMap_naturality {M N : (SheafOfModules.{u} (moduleRings Y))}
  (a : M ⟶ N)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
      (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)).map i ≫
      (ModuleCat.restrictScalars ((moduleRings X).obj.map i).hom).map
        ((ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app V).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a).val.app V)) =
    ((ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
      ((TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a).val.app U)) ≫
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf N)).map i := by
  exact SheafOfModules.changeOfRingsHom_naturality (tensorPullbackRingMap g)
    (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
    (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) i

/-- The tensor formula on morphisms, followed by module sheafification.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
private def tensorPullbackMap {M N : (SheafOfModules.{u} (moduleRings Y))} (a : M ⟶ N) :
    tensorPullbackObj g M ⟶ tensorPullbackObj g N :=
  (PresheafOfModules.sheafification (𝟙 (moduleRings X).obj)).map
    { app := fun U ↦
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a).val.app U)
      naturality := tensorPullbackPresheafMap_naturality g a }

/-- Tensor pullback preserves identities. Source: Stacks, Tag 0095
(blueprint: def-pc-module-pullback).
Proof: the abelian inverse-image functor preserves identities; its module map is the
same map with linearity supplied. Extension of scalars and sheafification preserve identities. -/
private theorem tensorPullbackMap_id (M : (SheafOfModules.{u} (moduleRings Y))) :
    tensorPullbackMap g (𝟙 M) = 𝟙 (tensorPullbackObj g M) := by
  let p :
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M) ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M) :=
    { app := fun U ↦
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M (𝟙 M)).val.app U)
      naturality := tensorPullbackPresheafMap_naturality g (𝟙 M) }
  have hp : p = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro U
    have hi :
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M (𝟙 M)).val.app U =
          𝟙 _ := by
      ext m
      simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
      rfl
    change (ModuleCat.extendScalars _).map _ = 𝟙 _
    rw [hi, CategoryTheory.Functor.map_id]
  change (PresheafOfModules.sheafification (𝟙 (moduleRings X).obj)).map p = _
  rw [hp, CategoryTheory.Functor.map_id]
  rfl

/-- Tensor pullback preserves composition. Source: Stacks, Tag 0095
(blueprint: def-pc-module-pullback).
Proof: the abelian inverse-image functor preserves composition; its module map is the
same map with linearity supplied. Extension of scalars and sheafification preserve composition. -/
private theorem tensorPullbackMap_comp {M N P : (SheafOfModules.{u} (moduleRings Y))} (a : M ⟶ N)
  (b : N ⟶ P) :
    tensorPullbackMap g (a ≫ b) = tensorPullbackMap g a ≫ tensorPullbackMap g b := by
  unfold tensorPullbackMap
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  have hi :
      (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M (a ≫ b)).val.app U =
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a).val.app U ≫
          (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf N b).val.app U := by
    ext m
    simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
    rfl
  change (ModuleCat.extendScalars _).map _ =
    (ModuleCat.extendScalars _).map _ ≫ (ModuleCat.extendScalars _).map _
  rw [hi, CategoryTheory.Functor.map_comp]

/-- Pullback of modules along a scheme morphism, defined by the tensor formula.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
private def tensorPullback : (SheafOfModules.{u} (moduleRings Y)) ⥤ (SheafOfModules.{u}
  (moduleRings X)) where
  obj := tensorPullbackObj g
  map := tensorPullbackMap g
  map_id := tensorPullbackMap_id g
  map_comp := tensorPullbackMap_comp g

private theorem tensorPullbackMap_toSheafify {M N : (SheafOfModules.{u} (moduleRings Y))} (a : M
  ⟶ N)
    (U : (Opens X)ᵒᵖ)
    (t : (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
      (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)).obj U) :
    (tensorPullbackMap g a).val.app U
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)).presheaf).app U t) =
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf N)).presheaf).app U
      ((ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
        ((TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a).val.app U) t) := by
  let p :
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M) ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf N) :=
    { app := fun V ↦
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app V).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a).val.app V)
      naturality := tensorPullbackPresheafMap_naturality g a }
  exact congrArg (fun q ↦ q.app U t)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (moduleRings X).obj)).unit_naturality p)

private abbrev tensorPullbackRingMapUnderlying :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (tensorPullbackRingMap g)

private abbrev tensorPullbackRingUnit : (moduleRings Y) ⟶
    ((Opens.map g.hom.base).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing g.hom.base Y.sheaf)) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map g.hom.base) CommRingCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app Y.sheaf)

private theorem tensorPullbackRingMap_unit :
    (tensorPullbackRingUnit g) ≫ ((Opens.map g.hom.base).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map
        (tensorPullbackRingMapUnderlying g) =
      (show moduleRings Y ⟶
        ((Opens.map g.hom.base).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
          (moduleRings X) from
        ⟨Functor.whiskerRight g.hom.c (forget₂ CommRingCat RingCat)⟩) := by
  have ht := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map g.hom.base) CommRingCat.{u} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology
      X)).homEquiv Y.sheaf X.sheaf
      |>.apply_symm_apply (show Y.sheaf ⟶
        ((Opens.map g.hom.base).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
          X.sheaf from ⟨g.hom.c⟩)
  rw [Adjunction.homEquiv_unit] at ht
  ext V r
  exact congrArg (fun t ↦ t.hom.app V r) ht

private def tensorPullbackPushforwardIso :
    SheafOfModules.restrictScalars (tensorPullbackRingMapUnderlying g) ⋙
      SheafOfModules.pushforward.{u} (tensorPullbackRingUnit g) ≅
      moduleDirectImage g :=
  (SheafOfModules.pushforwardComp (F := Opens.map g.hom.base) (G := 𝟭 (Opens X))
    (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing g.hom.base Y.sheaf))) (R' := (moduleRings X)) (S :=
          (moduleRings Y)) (tensorPullbackRingUnit g) (tensorPullbackRingMapUnderlying g)) ≪≫
    SheafOfModules.pushforwardCongr (tensorPullbackRingMap_unit g)

/-- The tensor formula is left adjoint to the sectionwise module pushforward.
Source: Stacks, Tag 0096 (blueprint: def-pc-module-pullback).
Proof: apply the tensor/restriction adjunction to the change of rings, then the
inverse-image/direct-image module adjunction (008Y). The resulting bijection is natural
and its right-hand module action is restriction along `g.hom.c`, hence the recorded pushforward.
These are the first two steps of this node, using lem-pc-module-pullback-adjunction. -/
private theorem nonempty_tensorPullbackAdjunction : Nonempty (tensorPullback g ⊣
  moduleDirectImage g) := by
  obtain ⟨E, h, adj, he⟩ := SheafOfModules.exists_changeOfRingsAdjunction (X : TopCat.{u})
    (TopCat.Sheaf.inverseImageRing g.hom.base Y.sheaf) X.sheaf (tensorPullbackRingMap g)
  obtain ⟨φ, hφ, _, _⟩ := SheafOfModules.moduleInverseImageAdjunction g.hom.base Y.sheaf
  let e : ∀ (M : (SheafOfModules.{u} (moduleRings Y))) (N : (SheafOfModules.{u} (moduleRings X))),
      (tensorPullbackObj g M ⟶ N) ≃ (M ⟶ (moduleDirectImage g).obj N) := fun M N ↦
    ((Iso.homCongr (eqToIso (h (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))).symm
      (Iso.refl N)).trans
      (adj.homEquiv (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M) N)).trans
      ((φ M ((SheafOfModules.restrictScalars (tensorPullbackRingMapUnderlying g)).obj N)).trans
        (Iso.homCongr (Iso.refl M) ((tensorPullbackPushforwardIso g).app N)))
  have eval (M : (SheafOfModules.{u} (moduleRings Y))) (N : (SheafOfModules.{u} (moduleRings X)))
    (a : tensorPullbackObj g M ⟶ N)
      (V : (Opens Y)ᵒᵖ) (m : M.val.obj V) :
      (e M N a).val.app V m =
        a.val.app ((Opens.map g.hom.base).op.obj V)
          ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
              (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)).presheaf).app
            ((Opens.map g.hom.base).op.obj V)
            ((1 : X.sheaf.obj.obj ((Opens.map g.hom.base).op.obj V)) ⊗ₜ[
              (TopCat.Sheaf.inverseImageRing g.hom.base Y.sheaf).obj.obj
                ((Opens.map g.hom.base).op.obj V),
              ((tensorPullbackRingMap g).hom.app ((Opens.map g.hom.base).op.obj V)).hom]
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (Opens.map g.hom.base) AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
                  (Opens.grothendieckTopology X)).unit.app
                  ((SheafOfModules.toSheaf _).obj M)).hom.app V m))) := by
    change (φ M ((SheafOfModules.restrictScalars (tensorPullbackRingMapUnderlying g)).obj N)
      ((adj.homEquiv _ _) (eqToHom (h _) ≫ a))).val.app V m = _
    rw [hφ]
    exact he _ _ a _ _
  have hl {M' M : (SheafOfModules.{u} (moduleRings Y))} {N : (SheafOfModules.{u} (moduleRings
    X))} (a : M' ⟶ M)
      (b : tensorPullbackObj g M ⟶ N) :
      e M' N (tensorPullbackMap g a ≫ b) = a ≫ e M N b := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext m
    let W := (Opens.map g.hom.base).op.obj V
    let adjAb := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map g.hom.base) AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)
    let x := ((adjAb.unit.app ((SheafOfModules.toSheaf _).obj M')).hom.app V m)
    have hn :
        (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M' a).val.app W x =
          (adjAb.unit.app ((SheafOfModules.toSheaf _).obj M)).hom.app V
            (a.val.app V m) := by
      exact congrArg (fun t ↦ t.hom.app V m)
        (adjAb.unit_naturality ((SheafOfModules.toSheaf _).map a))
    refine (eval M' N (tensorPullbackMap g a ≫ b) V m).trans ?_
    refine (congrArg (fun t ↦ b.val.app W t)
      (tensorPullbackMap_toSheafify g a W ((1 : X.sheaf.obj.obj W) ⊗ₜ[_, _] x))).trans ?_
    have ht :
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app W).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M' a).val.app W)
          ((1 : X.sheaf.obj.obj W) ⊗ₜ[_, _] x) =
        (1 : X.sheaf.obj.obj W) ⊗ₜ[_, ((tensorPullbackRingMap g).hom.app W).hom]
          (show (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M).val.obj W from
            (adjAb.unit.app ((SheafOfModules.toSheaf _).obj M)).hom.app V
              (a.val.app V m)) := by
      erw [ModuleCat.ExtendScalars.map_tmul]
      exact congrArg (fun y ↦ (1 : X.sheaf.obj.obj W) ⊗ₜ[_,
        ((tensorPullbackRingMap g).hom.app W).hom] y) hn
    exact (congrArg (fun t ↦ b.val.app W
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap g)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)).presheaf).app W t)) ht).trans
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
      (congrArg (fun x ↦ b.val.app ((Opens.map g.hom.base).op.obj V) x)
        (eval M N a V m).symm)


/-- The concrete inverse image followed by tensor change of rings is an additive
left adjoint to module direct image.

Source: Stacks Project, Sheaves, Tags 008A and 008Y.
(blueprint: lem-pc-ringed-space-tensor-pullback-underived)

Proof: take the inverse-image module Hom equivalence of Tag 008Y and compose
it with the extension/restriction-of-scalars equivalence of Tag 008A along the
adjoint structure map. The right composite is direct image with the scalar
structure through g-sharp: the adjunction triangle identity for the ring sheaves
identifies the composite ring map with g-sharp. The natural Hom equivalences
define the functor on objects and maps. On maps it is precisely inverse image
followed by the sheafification of the sectionwise map id tensor a, by naturality
of both equivalences. The inverse-image functor on abelian sheaves and the
sectionwise tensor functor are additive, as is sheafification, so their composite
is additive. This proves the prescribed object and morphism formulas and the
underived adjunction. -/
theorem exists_tensorModulePullback
    {X Y : RingedSpace.{u}} (g : X ⟶ Y) :
    ∃ (P : SheafOfModules.{u} (moduleRings Y) ⥤ SheafOfModules.{u} (moduleRings X))
      (h : ∀ M : SheafOfModules.{u} (moduleRings Y),
        P.obj M = SheafOfModules.changeOfRings.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M))
      (_ : ∀ {M N : SheafOfModules.{u} (moduleRings Y)} (a : M ⟶ N),
        P.map a = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
          (CochainComplex.tensorPullbackRingMap g.hom.base X.sheaf Y.sheaf ⟨g.hom.c⟩)
          (TopCat.Sheaf.inverseImageModule g.hom.base Y.sheaf M)
          (TopCat.Sheaf.inverseImageModuleMap g.hom.base Y.sheaf M a) ≫
          eqToHom (h N).symm)
      (_ : P.Additive),
      Nonempty (P ⊣ moduleDirectImage g) := by
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction g
  let := adj.isLeftAdjoint
  have ha : (tensorPullback g).Additive := by
    let := CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
      (tensorPullback g)
    exact Functor.additive_of_preservesBinaryBiproducts _
  refine ⟨tensorPullback g, fun _ ↦ rfl, ?_, ha, ⟨adj⟩⟩
  intro M N a
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end

end AlgebraicGeometry.RingedSpace
