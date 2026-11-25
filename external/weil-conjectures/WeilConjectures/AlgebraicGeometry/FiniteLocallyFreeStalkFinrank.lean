/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Stalk finrank of a finite locally free module

Source: Stacks Project, Tag 01C6, Definition 17.14.1 (3), and Tag 02G1.
(blueprint: lem-sc-finite-locally-free-stalk-finrank).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)

/-- Coordinate germs on neighbourhoods intersected with the trivializing open. -/
private noncomputable def coordinateCocone
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) where
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
private noncomputable def coordinateAdd
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.presheaf.stalk x →+ X.presheaf.stalk x :=
  (colimit.desc _ (coordinateCocone M x U hx π)).hom

/-- The coordinate cocone computes its stalk map on a representative germ. -/
private lemma coordinateAdd_germ
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hxV : x ∈ V) (m : Γ(M, V)) :
    coordinateAdd M x U hx π (M.presheaf.germ V x hxV m) =
      X.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩
        ((π.val.app (op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom
          (M.presheaf.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op m)) := by
  change (colimit.ι _ (op (⟨V, hxV⟩ : OpenNhds x)) ≫
    colimit.desc _ (coordinateCocone M x U hx π)) m = _
  rw [colimit.ι_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate germs respect the action of the structure-ring stalk. -/
private noncomputable def coordinateLinear
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  stalkLinearMapMk (coordinateAdd M x U hx π) fun V hxV r m ↦ by
    rw [coordinateAdd_germ, coordinateAdd_germ, Scheme.Modules.map_smul]
    rw [(π.val.app _).hom.map_smul]
    change X.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩ (_ * _) = _
    rw [map_mul, X.presheaf.germ_res_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Within the trivializing open, coordinates can be computed without intersecting. -/
private lemma coordinateLinear_germ_of_le
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
private noncomputable def localProjection {I : Type u} [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (j : I) :
    M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e.hom ≫ SheafOfModules.freeπ j

/-- A coordinate inclusion in the chosen local trivialization. -/
private noncomputable def localInclusion {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U :=
  SheafOfModules.ιFree j ≫ e.inv

/-- The germ of a local coordinate vector. -/
private noncomputable def localBasisGerm {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I) : M.presheaf.stalk x :=
  M.presheaf.germ U x hx
    ((localInclusion M U e j).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)))

set_option backward.isDefEq.respectTransparency false in
/-- Local coordinate vectors give the same germ after restriction. -/
private lemma localBasisGerm_eq {I : Type u}
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
private lemma local_sum {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) :
    ∑ j, localProjection M U e j ≫ localInclusion M U e j = 𝟙 (M.over U) := by
  simp only [localProjection, localInclusion, Category.assoc, ← Preadditive.comp_sum]
  simp_rw [← Category.assoc]
  rw [← Preadditive.sum_comp, SheafOfModules.sum_freeπ_ιFree,
    Category.id_comp, Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk coordinate vectors have Kronecker-delta coordinates. -/
private lemma coordinate_basis {I : Type u} [DecidableEq I]
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
private lemma sum_coordinate_basis {I : Type u} [Fintype I] [DecidableEq I]
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
private noncomputable def localStalkEquiv {I : Type u} [Fintype I] [DecidableEq I]
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
      simp_rw [LinearMap.map_smul, coordinate_basis]
      simp)

/-- A finite locally free module of fixed rank has that finrank at each stalk.
Source: Stacks Project, Tag 01C6, Definition 17.14.1 (3); the stalk calculation used
in Tag 02G1 (lemma-smooth-omega-finite-locally-free).
(blueprint: lem-sc-finite-locally-free-stalk-finrank).

Proof: take an open neighbourhood U of x on which M is a direct sum of r copies
of the structure sheaf. The coordinate projections and inclusions commute with
restrictions. Taking their germs gives mutually inverse linear maps between M_x
and (Fin r → O_{X,x}): the identities follow by taking germs of the coordinate
identities on U. Finite sums commute with germs, so this also works for r = 0.
Thus the coordinate vectors form a basis indexed by Fin r. Scheme local rings
are nontrivial commutative rings, so the basis cardinality computes finrank.
For the empty scheme there is no point x and the assertion is vacuous. -/
theorem finiteLocallyFreeOfRank_stalk_finrank {X : Scheme.{u}} (M : X.Modules) (r : ℕ)
    [M.IsFiniteLocallyFreeOfRank r] (x : X) :
    Module.finrank (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M) = r := by
  classical
  obtain ⟨I, U, hU, e⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.1
      (inferInstance : M.IsFiniteLocallyFreeOfRank r)
  obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hxV⟩ := hU ⊤ x trivial
  obtain ⟨e⟩ := e i
  have hx : x ∈ U i := g.le hxV
  let E := localStalkEquiv M x (U i) hx e
  change Module.finrank (X.presheaf.stalk x) (M.presheaf.stalk x) = r
  rw [E.finrank_eq]
  simp

end AlgebraicGeometry.Scheme.Modules
