/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCupProductMap
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction

/-! # Canonical comparisons for degree-zero Picard base change

Source: Stacks Project, Tags 0095, 0096, 08HY and 0BDP.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor pullback composition, transported from ordinary pullback.
Source: Stacks Project, Tags 0095 and 0096; uniqueness of left adjoints.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
noncomputable def picardTensorCompIso {A B C : Scheme.{u}}
    (k : A ⟶ B) (l : B ⟶ C) (M : C.Modules) :
    (tensorPullback k).obj ((tensorPullback l).obj M) ≅
      (tensorPullback (k ≫ l)).obj M :=
  (tensorPullback k).mapIso ((picardTensorComparison l).app M) ≪≫
    (picardTensorComparison k).app ((pullback l).obj M) ≪≫
      (pullbackComp k l).app M ≪≫ (picardTensorComparison (k ≫ l)).symm.app M

/-- The map between the non-iterated fibre products induced by a base morphism.
Source: Stacks Project, Tag 0BDP, change-of-base paragraph.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
noncomputable def picardBaseChangeTop {X S W T : Scheme.{u}}
    (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) :
    CategoryTheory.Limits.pullback f (h ≫ j) ⟶ CategoryTheory.Limits.pullback f j :=
  CategoryTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst f (h ≫ j))
    (CategoryTheory.Limits.pullback.snd f (h ≫ j) ≫ h)
    (by rw [Category.assoc]; exact CategoryTheory.Limits.pullback.condition)

/-- The canonical direct-image base-change map, with the top pullbacks composed.
Source: Stacks Project, Tags 08HY and 0BDP, change-of-base paragraph.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
noncomputable def picardDirectImageBaseChangeMap {X S W T : Scheme.{u}}
    (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules) :
    (tensorPullback h).obj
      ((pushforward (CategoryTheory.Limits.pullback.snd f j)).obj
        ((tensorPullback (CategoryTheory.Limits.pullback.fst f j)).obj M)) ⟶
    (pushforward (CategoryTheory.Limits.pullback.snd f (h ≫ j))).obj
      ((tensorPullback (CategoryTheory.Limits.pullback.fst f (h ≫ j))).obj M) :=
  let v := picardBaseChangeTop f j h
  moduleBaseChangeMap (CategoryTheory.Limits.pullback.snd f j)
    (CategoryTheory.Limits.pullback.snd f (h ≫ j)) h v
    (by dsimp [v, picardBaseChangeTop]; rw [CategoryTheory.Limits.pullback.lift_snd])
    ((tensorPullback (CategoryTheory.Limits.pullback.fst f j)).obj M) ≫
    (pushforward (CategoryTheory.Limits.pullback.snd f (h ≫ j))).map
      ((picardTensorCompIso v (CategoryTheory.Limits.pullback.fst f j) M).hom ≫
        (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj M)
          (by dsimp [v, picardBaseChangeTop];
              rw [CategoryTheory.Limits.pullback.lift_fst]))).hom)

/-- Pull evaluation back and transpose it; this fixes the dual comparison map.
Source: Stacks Project, Tag 0FNV, the coordinate dual basis computation.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
noncomputable def picardTensorDualComparison {W T : Scheme.{u}} (h : T ⟶ W)
    (M : W.Modules) : (tensorPullback h).obj (dual M) ⟶ dual ((tensorPullback h).obj M) :=
  MonoidalClosed.curry ((picardTensorObjIso h M (dual M)).inv ≫
    (tensorPullback h).map ((ihom.ev M).app (SheafOfModules.unit W.ringCatSheaf)) ≫
      (picardTensorUnitIso h).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
private theorem picardTensorObjIso_inv_naturality {W T : Scheme.{u}} (h : T ⟶ W)
    {A B C D : W.Modules} (f : A ⟶ B) (g : C ⟶ D) :
    ((tensorPullback h).map f ⊗ₘ (tensorPullback h).map g) ≫
        (picardTensorObjIso h B D).inv =
      (picardTensorObjIso h A C).inv ≫ (tensorPullback h).map (f ⊗ₘ g) := by
  simp only [picardTensorObjIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  erw [(picardTensorComparison h).hom.naturality f,
    (picardTensorComparison h).hom.naturality g]
  rw [← tensorHom_comp_tensorHom_assoc, Functor.Monoidal.μIso_hom,
    Functor.LaxMonoidal.μ_natural_assoc]
  erw [(picardTensorComparison h).inv.naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pulling a transpose back and applying the explicit dual comparison is currying
of the pulled pairing. This is naturality of the tensor comparison, followed by
injectivity of uncurrying. Source: Stacks Project, Tag 0095, tensor formula.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
private theorem picardTensorDualComparison_uncurry {W T : Scheme.{u}} (h : T ⟶ W)
    (M N : W.Modules) (g : N ⟶ dual M) :
    MonoidalClosed.uncurry ((tensorPullback h).map g ≫ picardTensorDualComparison h M) =
      (picardTensorObjIso h M N).inv ≫
        (tensorPullback h).map (MonoidalClosed.uncurry g) ≫ (picardTensorUnitIso h).hom := by
  rw [MonoidalClosed.uncurry_natural_left, picardTensorDualComparison,
    MonoidalClosed.uncurry_curry]
  rw [← id_tensorHom, ← (tensorPullback h).map_id,
    picardTensorObjIso_inv_naturality_assoc]
  rw [← Functor.map_comp_assoc, id_tensorHom, ← MonoidalClosed.uncurry_eq]

/-- A commuting square of pairings gives a commuting square of their transposes.
Source: Stacks Project, Tag 0BDP, transpose of the degree-zero cup pairing.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
private theorem picardTranspose_square {T : Scheme.{u}} {A A' B B' : T.Modules}
    (c : A ⟶ A') (a : B ⟶ B') (φ : B ⟶ dual A) (ψ : B' ⟶ dual A')
    (hpair : (c ⊗ₘ a) ≫ MonoidalClosed.uncurry ψ = MonoidalClosed.uncurry φ) :
    φ = (a ≫ ψ) ≫ dualMap c := by
  apply MonoidalClosed.uncurry_injective
  have hpre : dualMap c = (MonoidalClosed.pre c).app (SheafOfModules.unit T.ringCatSheaf) :=
    (pre_app c (SheafOfModules.unit T.ringCatSheaf)).symm
  rw [hpre, MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left]
  rw [← tensorHom_def_assoc]
  exact hpair.symm

/-- Invertible comparison maps and compatibility of pairings give a base-change
square for transposes. All isomorphisms are constructed from the specified maps.
Source: Stacks Project, Tag 0BDP, dualizing the degree-zero cup pairing.
(blueprint: lem-sc-picard-canonical-base-change-comparisons) -/
theorem picardBaseChangeSquare_of_pairings {W T : Scheme.{u}} (h : T ⟶ W)
    (N D : W.Modules) (NT DT : T.Modules)
    (φ : D ⟶ dual N) (ψ : DT ⟶ dual NT)
    (c : (tensorPullback h).obj N ⟶ NT) (a : (tensorPullback h).obj D ⟶ DT)
    [IsIso c] [IsIso a] [IsIso (picardTensorDualComparison h N)]
    (hpair : (c ⊗ₘ a) ≫ MonoidalClosed.uncurry ψ =
      (picardTensorObjIso h N D).inv ≫ (tensorPullback h).map (MonoidalClosed.uncurry φ) ≫
        (picardTensorUnitIso h).hom) :
    ∃ (aI : (tensorPullback h).obj D ≅ DT)
      (bI : (tensorPullback h).obj (dual N) ≅ dual NT),
      (tensorPullback h).map φ ≫ bI.hom = aI.hom ≫ ψ := by
  let d := asIso (picardTensorDualComparison h N)
  let cD := (dualFunctor T).mapIso (asIso c).symm.op
  have hpull := picardTensorDualComparison_uncurry h N D φ
  have key : (tensorPullback h).map φ ≫ d.hom = (a ≫ ψ) ≫ cD.inv :=
    picardTranspose_square c a _ _ (hpair.trans hpull.symm)
  refine ⟨asIso a, d ≪≫ cD, ?_⟩
  change (tensorPullback h).map φ ≫ (d.hom ≫ cD.hom) = _
  rw [← Category.assoc, key]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme.Modules
