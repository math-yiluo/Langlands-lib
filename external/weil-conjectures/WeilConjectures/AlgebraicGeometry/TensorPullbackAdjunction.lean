/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# The tensor-formula pullback of modules is left adjoint to pushforward

Source: Stacks Project, Tags 008X, 0095, 0096
(blueprint: lem-pc-module-pullback-adjunction).
-/

@[expose] public section

universe w

open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{w}} (g : X ⟶ Y)

/-- The canonical Hom bijection `Hom(P_g G, F) ≃ Hom(G, g_* F)` of Stacks 0096 is an
adjunction `tensorPullback g ⊣ pushforward g`. The adjunction is pinned to the canonical
composite by its unit: on a section `m` of `G` over `V` it is `θ(1 ⊗ η_G(m))`, where `η` is the
unit of the inverse-image/direct-image adjunction of abelian sheaves and `θ` is the
sheafification of the sectionwise tensor product.
Source: Stacks, Tag 0096 (blueprint: lem-pc-module-pullback-adjunction).
Proof: by the change-of-rings adjunction (Tag 008A), `Hom_{O_X}(P_g G, F)` is
`Hom_{g⁻¹O_Y}(g⁻¹G, F)` via `u ↦ (m ↦ u(1 ⊗ m))`. By the inverse-image/direct-image module
adjunction (Tag 008Y) this is `Hom_{O_Y}(G, g_* F)`, where `O_Y` acts on `g_* F` through
`ρ ∘ η_{O_Y}`. Since `ρ` is adjoint to `g^♯`, `ρ_{g⁻¹V} ∘ η_{O_Y,V} = g^♯_V`, so this is the
pushforward module. The composite bijection is natural in both modules, and its unit is
the stated sectionwise formula. -/
theorem exists_tensorPullbackAdjunction :
    ∃ adj : tensorPullback g ⊣ pushforward g,
      ∀ (G : Y.Modules) (V : (Opens Y)ᵒᵖ) (m : G.val.obj V),
        (adj.unit.app G).val.app V m =
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
              (TopCat.Sheaf.inverseImageModule g.base Y.sheaf G))).app
            ((Opens.map g.base).op.obj V)
            ((1 : X.sheaf.obj.obj ((Opens.map g.base).op.obj V)) ⊗ₜ[
              (TopCat.Sheaf.inverseImageRing g.base Y.sheaf).obj.obj ((Opens.map g.base).op.obj V),
              ((tensorPullbackRingMap g).hom.app ((Opens.map g.base).op.obj V)).hom]
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (Opens.map g.base) AddCommGrpCat.{w}
                (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app
                  ((SheafOfModules.toSheaf _).obj G)).hom.app V m)) := by
  -- Naturality of the sheafification unit on the explicit tensor presheaves.
  have tensorPullbackMap_toSheafify (g : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N)
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
  -- The composite ring action on direct image is the scheme structure map.
  let tensorPullbackRingMapUnderlying (g : X ⟶ Y) :=
    (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{w} RingCat.{w})).map (tensorPullbackRingMap g)
  let tensorPullbackRingUnit (g : X ⟶ Y) :=
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat.{w} RingCat.{w})).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map g.base) CommRingCat.{w} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app Y.sheaf)
  have tensorPullbackRingMap_unit (g : X ⟶ Y) :
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
  let tensorPullbackPushforwardIso (g : X ⟶ Y) :
      SheafOfModules.restrictScalars (tensorPullbackRingMapUnderlying g) ⋙
        SheafOfModules.pushforward.{w} (tensorPullbackRingUnit g) ≅
        pushforward g :=
    (SheafOfModules.pushforwardComp (F := Opens.map g.base) (G := 𝟭 (Opens X))
      (R := ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj
          (TopCat.Sheaf.inverseImageRing g.base Y.sheaf))) (R' := X.ringCatSheaf) (S :=
            Y.ringCatSheaf) (tensorPullbackRingUnit g) (tensorPullbackRingMapUnderlying g)) ≪≫
      SheafOfModules.pushforwardCongr (tensorPullbackRingMap_unit g)
  -- Compose the two canonical Hom equivalences, retaining their section formulas.
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
  -- Naturality makes this equivalence into an adjunction of the given functors.
  let core : Adjunction.CoreHomEquiv (tensorPullback g) (pushforward g) := by
    refine
      { homEquiv := e
        homEquiv_naturality_left_symm := ?_
        homEquiv_naturality_right := ?_ }
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
  -- The unit is the image of the identity under the canonical Hom equivalence.
  refine ⟨Adjunction.mkOfHomEquiv core, ?_⟩
  intro G V m
  rw [Adjunction.mkOfHomEquiv_unit_app]
  exact eval G (tensorPullbackObj g G) (𝟙 _) V m

end
end AlgebraicGeometry.Scheme.Modules
