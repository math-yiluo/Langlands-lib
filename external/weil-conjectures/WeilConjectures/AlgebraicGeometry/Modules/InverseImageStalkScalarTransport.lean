/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Topology.InverseImageStalk

/-!
# Scalar transport for inverse-image module stalks

This identifies two tensors of stalks before applying the stalk-of-change-of-rings
isomorphism. No tensor sheaf or pullback-module stalk occurs in the conclusion.

## References

* Stacks Project, Sheaves, Tags 008H and 0098
* Stacks Project, Sheaves, Tag 0098, proof using Tag 008H
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem explicitStalkComparison
    (C : Type (u + 1)) [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u} C FC]
    [CategoryTheory.Limits.HasColimits.{u} C] [CategoryTheory.Limits.HasLimits C]
    [CategoryTheory.Limits.PreservesLimits (CategoryTheory.forget C)]
    [CategoryTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {T Z : TopCat.{u}} (f : T ⟶ Z) (x : T) (G : Z.Sheaf C)
    (c : TopCat.Presheaf.stalk G.obj (f x) ≅
      TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback C f).obj G).obj x)
    (hc : ∀ (V : TopologicalSpace.Opens Z) (hx : f x ∈ V),
      TopCat.Presheaf.germ G.obj V (f x) hx ≫ c.hom =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app G).hom.app (op V) ≫
          TopCat.Presheaf.germ ((TopCat.Sheaf.pullback C f).obj G).obj
            ((Opens.map f).obj V) x hx) :
    ∃ d : TopCat.Presheaf.stalk G.obj (f x) ≅
      TopCat.Presheaf.stalk ((TopCat.Sheaf.inverseImageConstruction f C).obj G).obj x,
      ∀ (V : TopologicalSpace.Opens Z) (hx : f x ∈ V),
      TopCat.Presheaf.germ G.obj V (f x) hx ≫ d.hom =
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map f) C (Opens.grothendieckTopology Z)
          (Opens.grothendieckTopology T)).unit.app G).hom.app (op V) ≫
            TopCat.Presheaf.germ ((TopCat.Sheaf.inverseImageConstruction f C).obj G).obj
              ((Opens.map f).obj V) x hx := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
    C (Opens.grothendieckTopology Z) (Opens.grothendieckTopology T)
  let e := Adjunction.leftAdjointUniq (TopCat.Sheaf.pullbackPushforwardAdjunction C f) adj
  let d := c ≪≫ ((TopCat.Sheaf.forget C T) ⋙ TopCat.Presheaf.stalkFunctor C x).mapIso
    (e.app G)
  refine ⟨d, ?_⟩
  intro V hx
  change TopCat.Presheaf.germ G.obj V (f x) hx ≫
    (c.hom ≫ (TopCat.Presheaf.stalkFunctor C x).map (e.hom.app G).hom) = _
  rw [← Category.assoc, hc, Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  rw [← Category.assoc]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (TopCat.Sheaf.pullbackPushforwardAdjunction C f) adj G
  have hs := congrArg (fun q ↦ q.hom.app (op V)) hu
  exact congrArg (fun t ↦ t ≫ TopCat.Presheaf.germ
    ((TopCat.Sheaf.inverseImageConstruction f C).obj G).obj
      ((Opens.map f).obj V) x hx) hs

private theorem scalarTransport {A R S : Type u} [CommRing A] [CommRing R]
    [CommRing S] (φ : A →+* S) (ψ : R →+* S) (e : A ≃+* R)
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} R) (c : M ≃+ N)
    (hc : ∀ a m, c (a • m) = e a • c m)
    (he : ∀ a, ψ (e a) = φ a) :
    ∃ β : (ModuleCat.extendScalars φ).obj M ≅ (ModuleCat.extendScalars ψ).obj N,
      ∀ m, β.hom ((1 : S) ⊗ₜ[A, φ] m) = (1 : S) ⊗ₜ[R, ψ] c m := by
  let U := (ModuleCat.extendScalars φ).obj M
  let V := (ModuleCat.extendScalars ψ).obj N
  let ηM := (ModuleCat.extendRestrictScalarsAdj φ).unit.app M
  let ηN := (ModuleCat.extendRestrictScalarsAdj ψ).unit.app N
  let k : M ⟶ (ModuleCat.restrictScalars φ).obj V :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ).obj V)
    { toFun := fun m ↦ ηN (c m)
      map_add' := by intro m n; rw [c.map_add, map_add]
      map_smul' := by
        intro a m
        rw [hc]
        erw [ηN.hom.map_smul]
        change @SMul.smul S V _ (ψ (e a)) (ηN (c m)) =
          @SMul.smul S V _ (φ a) (ηN (c m))
        rw [he] }
  let l : N ⟶ (ModuleCat.restrictScalars ψ).obj U :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars ψ).obj U)
    { toFun := fun n ↦ ηM (c.symm n)
      map_add' := by intro m n; rw [c.symm.map_add, map_add]
      map_smul' := by
        intro r n
        have h : c.symm (r • n) = e.symm r • c.symm n := by
          apply c.injective
          rw [c.apply_symm_apply, hc, e.apply_symm_apply, c.apply_symm_apply]
        rw [h]
        erw [ηM.hom.map_smul]
        change @SMul.smul S U _ (φ (e.symm r)) (ηM (c.symm n)) =
          @SMul.smul S U _ (ψ r) (ηM (c.symm n))
        rw [← he, e.apply_symm_apply] }
  let b : U ⟶ V := (ModuleCat.ExtendRestrictScalarsAdj.homEquiv φ).symm k
  let d : V ⟶ U := (ModuleCat.ExtendRestrictScalarsAdj.homEquiv ψ).symm l
  have hb (m : M) : b ((1 : S) ⊗ₜ[A, φ] m) = (1 : S) ⊗ₜ[R, ψ] c m := by
    have h := (ModuleCat.ExtendRestrictScalarsAdj.homEquiv φ).apply_symm_apply k
    have hm := congrArg (fun q ↦ q m) h
    change b ((1 : S) ⊗ₜ[A, φ] m) = ηN (c m) at hm
    exact hm.trans (ModuleCat.extendRestrictScalarsAdj_unit_app_apply ψ N (c m))
  have hd (n : N) : d ((1 : S) ⊗ₜ[R, ψ] n) = (1 : S) ⊗ₜ[A, φ] c.symm n := by
    have h := (ModuleCat.ExtendRestrictScalarsAdj.homEquiv ψ).apply_symm_apply l
    have hn := congrArg (fun q ↦ q n) h
    change d ((1 : S) ⊗ₜ[R, ψ] n) = ηM (c.symm n) at hn
    exact hn.trans (ModuleCat.extendRestrictScalarsAdj_unit_app_apply φ M (c.symm n))
  refine ⟨{ hom := b, inv := d, hom_inv_id := ?_, inv_hom_id := ?_ }, hb⟩
  · apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change d (b ((1 : S) ⊗ₜ[A, φ] m)) = (1 : S) ⊗ₜ[A, φ] m
    rw [hb, hd, c.symm_apply_apply]
  · apply ModuleCat.ExtendScalars.hom_ext
    intro n
    change b (d ((1 : S) ⊗ₜ[R, ψ] n)) = (1 : S) ⊗ₜ[R, ψ] n
    rw [hd, hb, c.apply_symm_apply]

/-- Scalar transport through the inverse-image stalk isomorphisms. -/
theorem exists_inverseImage_stalk_scalar_transport {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    ∃ β : ∀ G : Y.Modules,
      (ModuleCat.extendScalars (f.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)).obj G) ≅
        (ModuleCat.extendScalars
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            (tensorPullbackRingMap f).hom).hom).obj
          (ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.toTopCat)
            (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
              (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G).val.presheaf x)),
      ∀ (G : Y.Modules) (V : Y.Opens) (hx : f x ∈ V) (s : G.val.obj (op V)),
        (β G).hom ((1 : X.presheaf.stalk x) ⊗ₜ[_, (f.stalkMap x).hom]
          (TopCat.Presheaf.germ G.val.presheaf V (f x) hx s)) =
        (1 : (TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.sheaf.obj) ⊗ₜ[
          TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.toTopCat)
          (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj x,
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            (tensorPullbackRingMap f).hom).hom]
          (TopCat.Presheaf.germ
            (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G).val.presheaf
            (f ⁻¹ᵁ V) x hx
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map f.base) AddCommGrpCat.{u}
              (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app
                ((SheafOfModules.toSheaf _).obj G)).hom.app (op V) s)) := by
  classical
  obtain ⟨cR₀, hcR₀, _⟩ :=
    TopCat.Sheaf.exists_inverseImage_stalk_iso_commRing f.base x
  obtain ⟨cR, hcR⟩ := explicitStalkComparison CommRingCat f.base x Y.sheaf
    (cR₀.app Y.sheaf) (by
      intro V hx
      ext s
      exact hcR₀ Y.sheaf V hx s)
  let e := cR.commRingCatIsoToRingEquiv
  let ψ := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
    (tensorPullbackRingMap f).hom).hom
  have he : ∀ a, ψ (e a) = (f.stalkMap x).hom a := by
    intro a
    obtain ⟨V, hx, a, rfl⟩ := Y.presheaf.exists_germ_eq a
    have hg := ConcreteCategory.congr_hom (hcR V hx) a
    change cR.hom (Y.presheaf.germ V (f x) hx a) = _ at hg
    change ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (tensorPullbackRingMap f).hom)
      (cR.hom (Y.presheaf.germ V (f x) hx a)) = _
    simp only [ConcreteCategory.comp_apply] at hg
    rw [hg]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    have hu := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).homEquiv Y.sheaf X.sheaf
      |>.apply_symm_apply (show Y.sheaf ⟶
        ((Opens.map f.base).sheafPushforwardContinuous CommRingCat.{u}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
          X.sheaf from ⟨f.c⟩)
    rw [Adjunction.homEquiv_unit] at hu
    have hs := congrArg (fun q ↦ q.hom.app (op V) a) hu
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact congrArg (fun t ↦ X.presheaf.germ (f ⁻¹ᵁ V) x hx t) hs
  obtain ⟨cA₀, hcA₀, _⟩ := TopCat.Sheaf.exists_inverseImage_stalk_iso_ab f.base x
  have hA (G : Y.Modules) :
      ∃ c : TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y.toTopCat) G.val.presheaf (f x) ≅
        TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
          (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G).val.presheaf x,
      ∀ (V : Y.Opens) (hx : f x ∈ V) (s : G.val.obj (op V)),
        c.hom (TopCat.Presheaf.germ G.val.presheaf V (f x) hx s) =
          TopCat.Presheaf.germ
            (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G).val.presheaf
            (f ⁻¹ᵁ V) x hx
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map f.base) AddCommGrpCat.{u}
              (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app
                ((SheafOfModules.toSheaf _).obj G)).hom.app (op V) s) := by
    let H := (SheafOfModules.toSheaf _).obj G
    obtain ⟨c, hc⟩ := explicitStalkComparison Ab f.base x H (cA₀.app H) (by
      intro V hx
      ext s
      exact hcA₀ H V hx s)
    refine ⟨c, ?_⟩
    intro V hx s
    exact ConcreteCategory.congr_hom (hc V hx) s
  choose cA hcA using hA
  have hsmul (G : Y.Modules) (a : Y.presheaf.stalk (f x))
      (m : TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y.toTopCat) G.val.presheaf (f x)) :
      (cA G).hom (a • m) = e a • (cA G).hom m := by
    obtain ⟨U, hxU, a, rfl⟩ := Y.presheaf.exists_germ_eq a
    obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf m
    have hx : f x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← Y.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) (f x) hx a,
      ← TopCat.Presheaf.germ_res_apply G.val.presheaf
        (homOfLE inf_le_right : U ⊓ V ⟶ V) (f x) hx m,
      ← PresheafOfModules.germ_smul (R := Y.presheaf) G.val]
    rw [hcA]
    have hu := (Classical.choose_spec
      (TopCat.Sheaf.exists_inverseImageModuleInstances f.base Y.sheaf G)).2
    have hs := hu (op (U ⊓ V))
      (Y.presheaf.map (homOfLE inf_le_left).op a)
      (G.val.map (homOfLE inf_le_right).op m)
    erw [hs]
    erw [PresheafOfModules.germ_smul
      (R := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj)
      (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G).val]
    rw [hcA]
    have hr := ConcreteCategory.congr_hom (hcR (U ⊓ V) hx)
      (Y.presheaf.map (homOfLE inf_le_left).op a)
    change cR.hom _ = _ at hr
    exact congrArg (fun r ↦ r • _) hr.symm
  have hβ (G : Y.Modules) := scalarTransport (f.stalkMap x).hom ψ e
    ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)).obj G)
    (ModuleCat.of
      (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.toTopCat)
        (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
        (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G).val.presheaf x))
    (cA G).addCommGroupIsoToAddEquiv (hsmul G) he
  choose β hβ using hβ
  refine ⟨β, ?_⟩
  intro G V hx s
  rw [hβ]
  exact congrArg (fun m : TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat)
      (TopCat.Sheaf.inverseImageModule f.base Y.sheaf G).val.presheaf x ↦
    (1 : (TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.sheaf.obj) ⊗ₜ[
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.toTopCat)
        (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj x, ψ] m) (hcA G V hx s)

end
end AlgebraicGeometry.Scheme.Modules
