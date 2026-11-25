/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Stalk of restriction along the relative inverse-image ring map

(blueprint: lem-pc-relative-inverse-image-stalk-restriction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem relative_ring_stalk_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : X) :
    (TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f.base Y.presheaf y ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj Y.presheaf))) ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
        (Modules.tensorPullbackRingMap f).hom = f.stalkMap y := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
  have hu := (adj.homEquiv Y.sheaf X.sheaf).apply_symm_apply
    (show Y.sheaf ⟶ _ from ⟨f.c⟩)
  rw [Adjunction.homEquiv_unit] at hu
  have hu0 (V : Opens Y) : (adj.unit.app Y.sheaf).hom.app (Opposite.op V) =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        f.base).unit.app Y.presheaf).app (Opposite.op V) ≫
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj Y.presheaf)).app
            (Opposite.op ((Opens.map f.base).obj V)) := by
    change ((sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).map
      (adj.unit.app Y.sheaf)).app _ = _
    dsimp only [adj, Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp [Adjunction.comp_unit_app, TopCat.Presheaf.pullbackPushforwardAdjunction,
      TopCat.Presheaf.pullback]
    rfl
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hV
  simp only [Category.assoc]
  rw [TopCat.Presheaf.germ_stalkPullbackHom_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rw [← Category.assoc, ← Category.assoc, ← hu0 V]
  have huv := congrArg (fun t ↦ t.hom.app (Opposite.op V)) hu
  change (adj.unit.app Y.sheaf).hom.app (Opposite.op V) ≫
    (Modules.tensorPullbackRingMap f).hom.app
      (Opposite.op ((Opens.map f.base).obj V)) = f.c.app (Opposite.op V) at huv
  rw [huv]
  exact (PresheafedSpace.stalkMap_germ f.toPshHom V y hV).symm

-- Comparing germ actions unfolds the module structures on both colimit stalks.
private theorem restriction_stalk_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : X)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    let Z : RingedSpace.{u} :=
      { carrier := X.carrier
        presheaf := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj
        IsSheaf := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).property }
    let T := SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
    let ψ := ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
      (Modules.tensorPullbackRingMap f).hom).hom
    ∀ (r : Z.presheaf.stalk y) (m : (RingedSpace.moduleStalkFunctor X.toRingedSpace y).obj M),
      r • (show (RingedSpace.moduleStalkFunctor Z y).obj (T.obj M) from m) = ψ r • m := by
  dsimp only
  intro r m
  obtain ⟨U, hU, r, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (X := X.carrier)
      (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj r
  obtain ⟨V, hV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  have hy : y ∈ U ⊓ V := ⟨hU, hV⟩
  rw [← TopCat.Presheaf.germ_res_apply (X := X.carrier)
    (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj
    (homOfLE inf_le_left : U ⊓ V ⟶ U) y hy r,
    ← TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE inf_le_right : U ⊓ V ⟶ V) y hy m]
  erw [← PresheafOfModules.germ_smul
    (R := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj)
    ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).obj M).val]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) M.val]
  rfl

/-- Taking a stalk after relative scalar restriction agrees with the scheme stalk map.
Source: Stacks Project, Sheaves Tags 008H and 0098; Modules Tag 01AG.
Proof: scalar restriction changes only the scalar action, so the underlying additive
stalks on both sides are the same. Write k for the inverse-image ring stalk map and
psi for the stalk of tensorPullbackRingMap f. The adjunction defining that ring map,
checked on germs of a section of O_Y on a neighborhood of f(y), gives psi k = f.stalkMap y.
Represent a scalar and a module element on a common neighborhood of y. The germ
formula for the module action then shows that the identity on the additive stalk
is linear for the two A-actions. These identities are natural in every sheaf morphism,
so their termwise identity isomorphisms commute with the differentials of K and
assemble into the displayed complex isomorphism. No K-flatness, boundedness or
quasi-isomorphism assumption is used. This includes zero modules and all degrees.
(blueprint: lem-pc-relative-inverse-image-stalk-restriction). -/
theorem relative_inverseImage_stalk_restriction_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : X)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let Z : RingedSpace.{u} :=
      { carrier := X.carrier
        presheaf := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj
        IsSheaf := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).property }
    let k := TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f.base Y.presheaf y ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj Y.presheaf))
    letI := RingedSpace.moduleStalkFunctor_preservesZeroMorphisms Z y
    Nonempty ((((ModuleCat.restrictScalars k.hom).mapHomologicalComplex (.up ℤ)).obj
      (((RingedSpace.moduleStalkFunctor Z y).mapHomologicalComplex (.up ℤ)).obj
      (((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
            (Modules.tensorPullbackRingMap f))).mapHomologicalComplex (.up ℤ)).obj K))) ≅
      (((ModuleCat.restrictScalars (f.stalkMap y).hom).mapHomologicalComplex (.up ℤ)).obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace y).mapHomologicalComplex
          (.up ℤ)).obj K))) := by
  let Z : RingedSpace.{u} :=
    { carrier := X.carrier
      presheaf := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).obj
      IsSheaf := (TopCat.Sheaf.inverseImageRing f.base Y.sheaf).property }
  let k := TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f.base Y.presheaf y ≫
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
      (toSheafify (Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj Y.presheaf))
  let T := SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
  let G := RingedSpace.moduleStalkFunctor Z y
  let H := RingedSpace.moduleStalkFunctor X.toRingedSpace y
  let U := ModuleCat.restrictScalars k.hom
  let V := ModuleCat.restrictScalars (f.stalkMap y).hom
  let := RingedSpace.moduleStalkFunctor_preservesZeroMorphisms Z y
  let := RingedSpace.moduleStalkFunctor_preservesZeroMorphisms X.toRingedSpace y
  have hs (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (r : Y.presheaf.stalk (f y)) (m : U.obj (G.obj (T.obj M))) :
      (r • m : U.obj (G.obj (T.obj M))) =
        (r • (show V.obj (H.obj M) from m) : V.obj (H.obj M)) := by
    change k.hom r • (show G.obj (T.obj M) from m) =
      (f.stalkMap y).hom r • (show H.obj M from m)
    rw [restriction_stalk_smul f y M]
    have hk := ConcreteCategory.congr_hom (relative_ring_stalk_map f y) r
    exact congrArg (fun t ↦ t • (show H.obj M from m)) hk
  let a (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
      U.obj (G.obj (T.obj M)) ≅ V.obj (H.obj M) :=
    ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext m; exact (hs M r m).symm)
  let E : T ⋙ G ⋙ U ≅ H ⋙ V := NatIso.ofComponents a (by intro M N f; ext m; rfl)
  exact ⟨(NatIso.mapHomologicalComplex E (.up ℤ)).app K⟩


end AlgebraicGeometry.Scheme
