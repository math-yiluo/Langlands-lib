/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity

/-!
# Sections and cocycles of a simultaneous étale Čech presentation

Source: Stacks Project, Tags 099S, 099T and 099U; finite representatives and eventual equality
in filtered colimits, Tag 002W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.AffineEtaleCechSystem

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable {Y : Scheme.{u}} {V : Y.ProEt} {n : ℕ} {U : Fin n → Over V}
  {I : Type u} [SmallCategory I] (S : AffineEtaleCechSystem Y V U I)
  (J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The ordinary ordered Čech complex at an étale stage. -/
noncomputable abbrev stageComplex (i : I) : CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (Presheaf.cechComplex (fun b ↦ Over.mk (S.f i b))).obj J.obj

/-- Restriction along the geometric transition maps, in every Čech degree. -/
noncomputable def transition {i j : I} (a : i ⟶ j) :
    S.stageComplex J j ⟶ S.stageComplex J i :=
  CochainComplex.ofHom
    (fun k ↦ AddCommGrpCat.ofHom (AddMonoidHom.pi fun y ↦
      (J.obj.map (S.trans a k y).op).hom.comp (Pi.evalAddMonoidHom _ y))) (by
      intro k
      apply AddCommGrpCat.ext
      intro c
      funext y
      change ((S.stageComplex J i).d k (k + 1)
        (fun z ↦ J.obj.map (S.trans a k z).op (c z))) y =
        J.obj.map (S.trans a (k + 1) y).op ((S.stageComplex J j).d k (k + 1) c y)
      rw [Presheaf.cechComplex_d_apply, Presheaf.cechComplex_d_apply, map_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [map_zsmul]
      congr 1
      rw [← ConcreteCategory.comp_apply, ← J.obj.map_comp, ← op_comp,
        ← ConcreteCategory.comp_apply, ← J.obj.map_comp, ← op_comp]
      rw [S.trans_face])

/-- The filtered diagram of stage Čech complexes. -/
noncomputable def diagram : Iᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ where
  obj i := S.stageComplex J i.unop
  map a := S.transition J a.unop
  map_id i := by
    ext k : 1
    apply AddCommGrpCat.ext
    intro c
    funext y
    change J.obj.map (S.trans (𝟙 i.unop) k y).op (c y) = c y
    rw [S.trans_id, op_id, J.obj.map_id]
    rfl
  map_comp a b := by
    ext k : 1
    apply AddCommGrpCat.ext
    intro c
    funext y
    change J.obj.map (S.trans (b.unop ≫ a.unop) k y).op (c y) =
      J.obj.map (S.trans b.unop k y).op (J.obj.map (S.trans a.unop k y).op (c y))
    rw [S.trans_comp, op_comp, J.obj.map_comp]
    rfl

/-- The comparison unit, followed by restriction along the presentation cone. -/
noncomputable def toOriginal (i : I) :
    S.stageComplex J i ⟶ (Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj := by
  let F := ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj
  let η := ((comparisonAdjunction AddCommGrpCat.{u + 1} Y).unit.app J).hom
  refine CochainComplex.ofHom (fun k ↦ AddCommGrpCat.ofHom
    (AddMonoidHom.pi fun y ↦ ((F.map (S.π k y i).op).hom.comp
      (η.app (op ((S.nerve k y).obj i))).hom).comp (Pi.evalAddMonoidHom _ y))) ?_
  intro k
  apply AddCommGrpCat.ext
  intro c
  funext y
  change ((Presheaf.cechComplex U).obj F).d k (k + 1)
      (fun z ↦ F.map (S.π k z i).op (η.app _ (c z))) y =
    F.map (S.π (k + 1) y i).op (η.app _ ((S.stageComplex J i).d k (k + 1) c y))
  rw [Presheaf.cechComplex_d_apply, Presheaf.cechComplex_d_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_zsmul, map_zsmul]
  congr 1
  have hη := ConcreteCategory.congr_hom
    (η.naturality (Presheaf.cechNerveMap (fun b ↦ Over.mk (S.f i b)) y l.succAbove).left.op)
    (c (y ∘ l.succAbove))
  change F.map (Presheaf.cechNerveMap U y l.succAbove).left.op
      (F.map (S.π k (y ∘ l.succAbove) i).op (η.app _ (c (y ∘ l.succAbove)))) = _
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, S.π_face,
    op_comp, F.map_comp]
  exact congrArg (fun x ↦ F.map (S.π (k + 1) y i).op x) hη.symm

/-- These maps form a cocone of complexes. -/
noncomputable def cocone : Cocone (S.diagram J) where
  pt := (Presheaf.cechComplex U).obj
    ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj
  ι.app i := S.toOriginal J i.unop
  ι.naturality i j a := by
    ext k : 1
    apply AddCommGrpCat.ext
    intro c
    funext y
    let F := ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj
    let η := ((comparisonAdjunction AddCommGrpCat.{u + 1} Y).unit.app J).hom
    change F.map (S.π k y j.unop).op
        (η.app _ (J.obj.map (S.trans a.unop k y).op (c y))) =
      F.map (S.π k y i.unop).op (η.app _ (c y))
    have hη := ConcreteCategory.congr_hom (η.naturality (S.trans a.unop k y).op) (c y)
    change η.app _ (J.obj.map (S.trans a.unop k y).op (c y)) =
      F.map ((Scheme.toProEt Y).map (S.trans a.unop k y)).op (η.app _ (c y)) at hη
    rw [hη, ← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, S.π_naturality]

end AlgebraicGeometry.ProEtale.AffineEtaleCechSystem
