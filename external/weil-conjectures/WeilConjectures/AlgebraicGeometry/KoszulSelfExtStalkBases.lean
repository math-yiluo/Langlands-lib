/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.KoszulSelfExtPullbackLocalFrame
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.AlgebraicGeometry.AffineConormalFrame
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison

/-! # Finite bases for self Ext and exterior stalks on a Koszul chart

Source: Stacks Project, Tags 0BQY, 062I and 01R3. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

-- Local coordinate germs, following the proved stalk calculation of
-- WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank (group S3).

/-- Coordinate germs on neighbourhoods intersected with the trivializing open. -/
private noncomputable def coordinateCocone {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Cocone ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of (X.presheaf.stalk x)
  ι :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        (((X.presheaf.germ (V.unop.1 ⊓ U) x ⟨V.unop.2, hx⟩).hom.toAddMonoidHom).comp
          (((π.val.app (op (Over.mk
            (homOfLE inf_le_right : V.unop.1 ⊓ U ⟶ U)))).hom.toAddMonoidHom).comp
            (M.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op).hom))
      naturality := by
        intro V W f
        ext m
        let a : W.unop.1 ⊓ U ⟶ V.unop.1 ⊓ U := homOfLE (inf_le_inf f.unop.le le_rfl)
        let a' : Over.mk (homOfLE inf_le_right : W.unop.1 ⊓ U ⟶ U) ⟶
            Over.mk (homOfLE inf_le_right : V.unop.1 ⊓ U ⟶ U) := Over.homMk a
        have hπ := ConcreteCategory.congr_hom (π.val.naturality a'.op)
          (M.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op m)
        change X.presheaf.germ (W.unop.1 ⊓ U) x ⟨W.unop.2, hx⟩
          ((π.val.app (op (Over.mk (homOfLE inf_le_right : W.unop.1 ⊓ U ⟶ U)))).hom
            (M.presheaf.map (homOfLE inf_le_left : W.unop.1 ⊓ U ⟶ W.unop.1).op
              (M.presheaf.map (homOfLE f.unop.le : W.unop.1 ⟶ V.unop.1).op m))) =
          X.presheaf.germ (V.unop.1 ⊓ U) x ⟨V.unop.2, hx⟩
            ((π.val.app (op (Over.mk (homOfLE inf_le_right : V.unop.1 ⊓ U ⟶ U)))).hom
              (M.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op m))
        rw [← M.presheaf.map_comp_apply]
        have hw : (homOfLE f.unop.le : W.unop.1 ⟶ V.unop.1).op ≫
            (homOfLE inf_le_left : W.unop.1 ⊓ U ⟶ W.unop.1).op =
            (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op ≫ a.op :=
          Subsingleton.elim _ _
        rw [hw, M.presheaf.map_comp_apply]
        rw [← X.presheaf.germ_res_apply a x ⟨W.unop.2, hx⟩]
        congr 1 }

/-- The additive map on stalks determined by local coordinate germs. -/
private noncomputable def coordinateAdd {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.presheaf.stalk x →+ X.presheaf.stalk x :=
  (colimit.desc _ (coordinateCocone M x U hx π)).hom

/-- The coordinate cocone computes its stalk map on a representative germ. -/
private lemma coordinateAdd_germ {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hxV : x ∈ V) (m : Γ(M, V)) :
    coordinateAdd M x U hx π (M.presheaf.germ V x hxV m) =
      X.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩
        ((π.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom
          (M.presheaf.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op m)) := by
  change (colimit.ι _ (op (⟨V, hxV⟩ : TopologicalSpace.OpenNhds x)) ≫
    colimit.desc _ (coordinateCocone M x U hx π)) m = _
  rw [colimit.ι_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate germs respect the action of the structure-ring stalk. -/
private noncomputable def coordinateLinear {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  stalkLinearMapMk (coordinateAdd M x U hx π) fun V hxV r m ↦ by
    rw [coordinateAdd_germ, coordinateAdd_germ,
      Scheme.Modules.map_smul]
    rw [(π.val.app _).hom.map_smul]
    change X.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩ (_ * _) = _
    rw [map_mul, X.presheaf.germ_res_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Within the trivializing open, coordinates can be computed without intersecting. -/
private lemma coordinateLinear_germ_of_le {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U) (m : Γ(M, V)) :
    coordinateLinear M x U hx π (M.presheaf.germ V x hxV m) =
      X.presheaf.germ V x hxV
        ((π.val.app (op (Over.mk (homOfLE hVU)))).hom m) := by
  change coordinateAdd M x U hx π (M.presheaf.germ V x hxV m) = _
  rw [coordinateAdd_germ]
  let a : V ⊓ U ⟶ V := homOfLE inf_le_left
  let a' : Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U) ⟶
      Over.mk (homOfLE hVU : V ⟶ U) := Over.homMk a
  have hπ := ConcreteCategory.congr_hom (π.val.naturality a'.op) m
  have he : (π.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom
      (M.presheaf.map a.op m) =
      X.presheaf.map a.op ((π.val.app (op (Over.mk (homOfLE hVU)))).hom m) :=
    hπ
  rw [he, X.presheaf.germ_res_apply]

/-- A coordinate projection in the chosen local trivialization. -/
private noncomputable def localProjection {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    {I : Type u} [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (j : I) :
    M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e.hom ≫ SheafOfModules.freeπ j

/-- A coordinate inclusion in the chosen local trivialization. -/
private noncomputable def localInclusion {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U :=
  SheafOfModules.ιFree j ≫ e.inv

/-- The germ of a local coordinate vector. -/
private noncomputable def localBasisGerm {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I) : M.presheaf.stalk x :=
  M.presheaf.germ U x hx
    ((localInclusion M U e j).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)))

set_option backward.isDefEq.respectTransparency false in
/-- Local coordinate vectors give the same germ after restriction. -/
private lemma localBasisGerm_eq {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I)
    (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U) :
    localBasisGerm M x U hx e j = M.presheaf.germ V x hxV
      ((localInclusion M U e j).val.app (op (Over.mk (homOfLE hVU))) (1 : Γ(X, V))) := by
  let a' : Over.mk (homOfLE hVU : V ⟶ U) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE hVU)
  have he := ConcreteCategory.congr_hom
    ((localInclusion M U e j).val.naturality a'.op) (1 : Γ(X, U))
  change localBasisGerm M x U hx e j = _
  unfold localBasisGerm
  rw [← M.presheaf.germ_res_apply (homOfLE hVU) x hxV]
  congr 1
  change (localInclusion M U e j).val.app (op (Over.mk (homOfLE hVU)))
      (X.presheaf.map (homOfLE hVU).op (1 : Γ(X, U))) =
    M.presheaf.map (homOfLE hVU).op
      ((localInclusion M U e j).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) at he
  rw [map_one] at he
  exact he.symm

/-- The sum of the coordinate projection-inclusion composites is the identity. -/
private lemma local_sum {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) :
    ∑ j, localProjection M U e j ≫ localInclusion M U e j = 𝟙 (M.over U) := by
  simp only [localProjection, localInclusion, Category.assoc, ← Preadditive.comp_sum]
  simp_rw [← Category.assoc]
  rw [← Preadditive.sum_comp, SheafOfModules.sum_freeπ_ιFree,
    Category.id_comp, Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk coordinate vectors have Kronecker-delta coordinates. -/
private lemma coordinate_basis {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U) {I : Type u} [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (j k : I) :
    coordinateLinear M x U hx (localProjection M U e j)
      (localBasisGerm M x U hx e k) = if k = j then 1 else 0 := by
  unfold localBasisGerm
  rw [coordinateLinear_germ_of_le M x U hx _ U hx le_rfl]
  have hp : localInclusion M U e k ≫ localProjection M U e j =
      if k = j then 𝟙 _ else 0 := by
    simp only [localInclusion, localProjection, Category.assoc, Iso.inv_hom_id_assoc,
      SheafOfModules.ιFree_freeπ]
  have he := congrArg (fun g ↦
    (g.val.app (op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))) hp
  change (localProjection M U e j).val.app (op (Over.mk (𝟙 U)))
      ((localInclusion M U e k).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) =
    _ at he
  change X.presheaf.germ U x hx
    ((localProjection M U e j).val.app (op (Over.mk (𝟙 U)))
      ((localInclusion M U e k).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)))) = _
  split_ifs at he ⊢ with h
  · change (localProjection M U e j).val.app (op (Over.mk (𝟙 U)))
        ((localInclusion M U e k).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = (1 : Γ(X, U)) at he
    exact (congrArg (fun a : Γ(X, U) ↦ X.presheaf.germ U x hx a) he).trans (map_one _)
  · change (localProjection M U e j).val.app (op (Over.mk (𝟙 U)))
        ((localInclusion M U e k).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = (0 : Γ(X, U)) at he
    exact (congrArg (fun a : Γ(X, U) ↦ X.presheaf.germ U x hx a) he).trans (map_zero _)

set_option backward.isDefEq.respectTransparency false in
/-- Every germ is the sum of its coordinates times the local basis germs. -/
private lemma sum_coordinate_basis {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U) {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (m : M.presheaf.stalk x) :
    ∑ j, coordinateLinear M x U hx (localProjection M U e j) m •
      localBasisGerm M x U hx e j = m := by
  obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hx
  simp_rw [coordinateLinear_germ_of_le M x U hx _ V hxV hVU,
    localBasisGerm_eq M x U hx e _ V hxV hVU, ← Scheme.Modules.germ_smul]
  rw [← map_sum]
  congr 1
  have he := congrArg (fun g ↦
    (g.val.app (op (Over.mk (homOfLE hVU)))).hom m) (local_sum M U e)
  rw [SheafOfModules.sum_val_app_apply] at he
  change ∑ j, (localInclusion M U e j).val.app (op (Over.mk (homOfLE hVU)))
      ((localProjection M U e j).val.app (op (Over.mk (homOfLE hVU))) m) = m at he
  calc
    _ = ∑ j, (localInclusion M U e j).val.app (op (Over.mk (homOfLE hVU)))
        ((localProjection M U e j).val.app (op (Over.mk (homOfLE hVU))) m) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← ((localInclusion M U e j).val.app _).hom.map_smul]
      congr 1
      exact mul_one (show Γ(X, V) from
        (localProjection M U e j).val.app (op (Over.mk (homOfLE hVU))) m)
    _ = m := he

/-- A finite local trivialization induces an explicit linear equivalence on stalks. -/
private noncomputable def localStalkEquiv {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U) {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] (I → X.presheaf.stalk x) :=
  LinearEquiv.ofBijective (LinearMap.pi fun j ↦
    coordinateLinear M x U hx (localProjection M U e j)) (by
    constructor
    · intro m n h
      rw [← sum_coordinate_basis M x U hx e m, ← sum_coordinate_basis M x U hx e n]
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun a ↦ a • localBasisGerm M x U hx e j) (congrFun h j)
    · intro c
      refine ⟨∑ j, c j • localBasisGerm M x U hx e j, ?_⟩
      ext k
      change coordinateLinear M x U hx (localProjection M U e k) _ = c k
      rw [map_sum]
      simp_rw [LinearMap.map_smul, coordinate_basis M x U hx e _ _]
      simp)

/-- Restrict a finite frame to the inverse image of its trivializing open. -/
private noncomputable def restrictLocalFrame
    {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) :
    (M.restrict V.ι).over (V.ι ⁻¹ᵁ U) ≅ SheafOfModules.free I :=
  (overIsoFreeEquiv (M.restrict V.ι) (V.ι ⁻¹ᵁ U) I).symm
    (((restrictFunctorComp _ _).app M).symm ≪≫
      restrictCompIso M U.ι (V.ι ∣_ U) ((V.ι ⁻¹ᵁ U).ι ≫ V.ι)
        (morphismRestrict_ι V.ι U) ≪≫
      (restrictFunctor _).mapIso (overIsoFreeEquiv M U I e) ≪≫ restrictFreeIso _ _)

/-- Taking coordinate germs of a finite frame gives a basis after open restriction. -/
private theorem restricted_stalk_basis
    {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens) (x : V.toScheme)
    (hx : x.1 ∈ U) {I : Type u} [Finite I]
    (e : M.over U ≅ SheafOfModules.free I) :
    Nonempty (Module.Basis I (V.toScheme.presheaf.stalk x)
      ((M.restrict V.ι).presheaf.stalk x)) := by
  classical
  let := Fintype.ofFinite I
  let eV := restrictLocalFrame M U V e
  let c := localStalkEquiv (M.restrict V.ι) x (V.ι ⁻¹ᵁ U) hx eV
  exact ⟨(Pi.basisFun (V.toScheme.presheaf.stalk x) I).map c.symm⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The self Ext stalk and exterior stalk have finite bases with the same index
set on a single Koszul-regular chart. No compatibility of the two bases is asserted.

Source: Stacks Project, Tag 0BQY, the zero-differential Hom calculation;
Tags 062I and 01R3 for the conormal basis.
(blueprint: lem-sc-koszul-self-ext-stalk-bases).

Proof: Let A be the section ring of U, I its closed-immersion ideal and B=A/I.
Sheafify the actual augmented Koszul projective resolution of B. Restriction of
derived internal Hom and the bounded finite free Hom model compute self Ext on U
as Hom of this resolution into B. The differential is zero because all regular
generators act by zero on B. Its degree n is the dual of the nth exterior power
of A^m with coefficients in B. The increasing wedge basis gives a B-basis indexed
by n-element subsets of Fin m. Sheafification, tensor pullback after cohomology,
restriction to V and then the stalk at z transport this to the first basis.
Independently, the regular conormal classes form a B-basis of I/I². The affine
conormal frame makes its sheaf locally free of rank m. Internal duality gives
the dual frame and the exterior sheaf local-free comparison gives its increasing
wedge frame with the same index set. Restrict and take germs of this frame to
obtain the second basis. Finite coordinate projections and inclusions show that
these germs form a basis over the stalk ring of V. Use a common K-injective model
for derived-universe comparison. The index set is a singleton for n=0 and empty
for n>m; empty charts cannot contain z. Only regularity on U is used. -/
theorem koszulRegularImmersion_self_ext_stalk_bases
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (z : V.toScheme) (U : Y.affineOpens) (hzU : i z.1 ∈ U.1)
    (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let E := Scheme.Modules.exteriorPower
      ((Scheme.Modules.restrictFunctor V.ι).obj
        (SheafOfModules.homObj (R := Z.sheaf)
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
          (SheafOfModules.unit Z.ringCatSheaf))) n
    Nonempty (Module.Basis (Set.powersetCard (Fin m) n)
      (V.toScheme.presheaf.stalk z) (T.presheaf.stalk z)) ∧
    Nonempty (Module.Basis (Set.powersetCard (Fin m) n)
      (V.toScheme.presheaf.stalk z) (E.presheaf.stalk z)) := by
  classical
  intro B S H G T E
  constructor
  · have hT : Nonempty
        ((((Scheme.Modules.tensorPullback i).obj G).over (i ⁻¹ᵁ U.1)) ≅
          SheafOfModules.free (ULift.{u} (Set.powersetCard (Fin m) n))) :=
      koszulRegularImmersion_self_ext_pullback_local_frame.{u, w} i U n m f hf hreg
    obtain ⟨eT⟩ := hT
    obtain ⟨bT⟩ := Scheme.Modules.restricted_stalk_basis (X := Z)
      (I := ULift.{u} (Set.powersetCard (Fin m) n))
      ((Scheme.Modules.tensorPullback i).obj G) (i ⁻¹ᵁ U.1) V z hzU eT
    exact ⟨bT.reindex Equiv.ulift⟩
  · let C := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let D : Z.Modules := SheafOfModules.homObj (R := Z.sheaf) C
      (SheafOfModules.unit Z.ringCatSheaf)
    let W := i ⁻¹ᵁ U.1
    obtain ⟨b, _⟩ := ExteriorAlgebra.exists_koszul_conormal_basis
      Γ(Y, U.1) (i.ker.ideal U) m f hreg hf
    obtain ⟨eC⟩ := (affine_conormal_frame i U m b).1
    let eD : D.over W ≅ SheafOfModules.free (ULift.{u} (Fin m)) :=
      SheafOfModules.overHomObjIso C (SheafOfModules.unit Z.ringCatSheaf) W ≪≫
        ((SheafOfModules.homFunctor (Z.sheaf.over W)).flip.obj
          (SheafOfModules.unit (Z.ringCatSheaf.over W))).mapIso eC.symm.op ≪≫
        SheafOfModules.homObjFreeUnitIso.{u} (R := Z.sheaf.over W)
          (ULift.{u} (Fin m))
    let eDV := Scheme.Modules.restrictLocalFrame D W V eD
    obtain ⟨eE⟩ := (Scheme.Modules.exteriorSheaf_local_free_comparison V.toScheme
      (D.restrict V.ι) n (V.ι ⁻¹ᵁ W) m eDV).1
    let c := Scheme.Modules.localStalkEquiv
      (Scheme.Modules.exteriorPower (D.restrict V.ι) n) z (V.ι ⁻¹ᵁ W) hzU eE
    exact ⟨((Pi.basisFun (V.toScheme.presheaf.stalk z)
      (ULift.{u} (Set.powersetCard (Fin m) n))).map c.symm).reindex Equiv.ulift⟩

end AlgebraicGeometry
