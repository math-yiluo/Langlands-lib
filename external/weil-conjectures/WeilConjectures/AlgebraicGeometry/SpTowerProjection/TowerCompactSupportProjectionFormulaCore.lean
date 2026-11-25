/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation

/-!
# Tower compact-support projection over an arbitrary standing field

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-integral-adjunction,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-tower-compact-support-projection-formula).

The section-site model, its tensor and all geometric operations are the recorded
SpTowerShriek operations. Constructibility is transported from the recorded full
subcategory of the ordinary derived category of coefficient towers. No normalization
or etale-origin witness is imposed. Index n always means positive exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerProjection

open SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Exact derived transport of the recorded sectionwise realization of towers.
Source: blueprint paragraph (3), ordinary tower category
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def realization (b : Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T A ≌ D l E T :=
  letI := A.hasDerived
  letI := b.realizationAdditive T
  (b.realization T).mapDerivedCategory

/-- The proper counit transpose, formed before any finite-level test or Tor hypothesis.
Source: blueprint paragraph (3), pi_p
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def properMap (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : D l E X) (B : D l E Y) :
    (tensor l E b Y).obj ((F l E b o c).obj C, B) ⟶
      (push l E b (o.geometry c.g)).obj
        ((tensor l E b c.Z).obj ((openD l E b (o.openOp c.i)).obj C,
          (pull l E b (o.geometry c.g)).obj B)) :=
  ((adjunction l E b (o.geometry c.g)).homEquiv _ _)
    (((o.geometry c.g).tensorPullback).hom.app ((F l E b o c).obj C, B) ≫
      (tensor l E b c.Z).map (Prod.mkHom
        ((adjunction l E b (o.geometry c.g)).counit.app
          ((openD l E b (o.openOp c.i)).obj C)) (𝟙 _)))

/-- The open-unit transpose pi_j, then Rp_*. The dependency's openTensor_mate fixes
its inverse direction as exactly that transpose, including the pullback/tensor comparison.
Source: blueprint paragraph (3), Rp_*(pi_j)
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def openMap (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : D l E X) (B : D l E Y) :=
  (push l E b (o.geometry c.g)).map
    ((o.openTensor c.i C ((pull l E b (o.geometry c.g)).obj B)).inv)

/-- The source of the proper projection arrow, as a functor of both inputs.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def source (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((F l E b o c).prod (𝟭 (D l E Y))) ⋙ tensor l E b Y

/-- The common target of the two arrows, as a functor of both inputs.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def middle (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((openD l E b (o.openOp c.i)).prod (pull l E b (o.geometry c.g))) ⋙
    tensor l E b c.Z ⋙ push l E b (o.geometry c.g)

/-- The source of the open projection arrow, using j^{-1}p^{-1}=f^{-1}.
The comparison to the single pullback is the recorded o.comp followed by c.comm.
Source: blueprint paragraph (3), naturality
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def openSource (b : Base l E) (o : Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((𝟭 (D l E X)).prod
    (pull l E b (o.geometry c.g) ⋙ pull l E b (o.geometry c.i))) ⋙
      tensor l E b X ⋙ F l E b o c

/-- The finite-level tensor is the same recorded K-flat total tensor.
Source: blueprint paragraph (3), finite projection maps
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
abbrev levelTensor (b : Base l E) (T : Scheme.{u}) (n : ℕ) :=
  ((b.calculus T).levelClosed n).tensor

/-- The finite inverse-image/tensor comparison in the normalized evaluated coordinates.
Every factor is a specified comparison of the section model. Its representative map is
therefore the canonical pure-tensor pullback comparison by Geometry.tensorPullback_eq.
Source: blueprint paragraph (3), finite projection maps
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def levelPullTensor (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (n : ℕ) (N B : D l E Y) :=
  (proEtaleConstantRingDerivedPullback (R l E n) f).mapIso
      (((b.calculus Y).tensorEvaluation n).app (N, B)).symm ≪≫
    ((g.pullEvaluation n).app ((tensor l E b Y).obj (N, B))).symm ≪≫
    (Ev l E X n).mapIso (g.tensorPullback.app (N, B)) ≪≫
    ((b.calculus X).tensorEvaluation n).app
      ((pull l E b g).obj N, (pull l E b g).obj B) ≪≫
    (levelTensor l E b X n).mapIso
      (((g.pullEvaluation n).app N).prod ((g.pullEvaluation n).app B))

/-- The finite derived inverse-image/direct-image adjunction, with its canonical
ordinary normalization. Source: blueprint paragraph (3), finite proper projection
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
abbrev levelAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (proEtaleConstantRingAdjunction (R l E n) f).mapDerivedCategoryRightDerivedAdjunction

/-- The finite proper projection map: the finite counit transpose of the canonical
finite pullback/tensor comparison. Evaluation comparisons only change coordinates;
the arrow is constructed by the finite adjunction, independently of properMap.
Source: blueprint paragraph (3), finite proper projection map
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def finiteProperMap (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) (n : ℕ) (N : D l E X) (B : D l E Y) :=
  ((levelAdjunction l E f n).homEquiv _ _)
    ((proEtaleConstantRingDerivedPullback (R l E n) f).map
        ((levelTensor l E b Y n).map
          (Prod.mkHom ((g.pushEvaluation n).inv.app N) (𝟙 _))) ≫
      (levelPullTensor l E b g n ((push l E b g).obj N) B).hom ≫
      (levelTensor l E b X n).map (Prod.mkHom
        ((proEtaleConstantRingDerivedPullback (R l E n) f).map
            ((g.pushEvaluation n).hom.app N) ≫
          (levelAdjunction l E f n).counit.app ((Ev l E X n).obj N))
        (𝟙 _)))

/-- The finite exact open adjunction, obtained by termwise localization of the
specified finite ordinary adjunction. No adjunction is chosen independently.
Source: blueprint paragraph (3), finite open projection map
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def levelOpenAdjunction (b : Base l E) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (n : ℕ) :
    sfIntrinsicDerivedOpen (R l E n) j ⊣
      proEtaleConstantRingDerivedPullback (R l E n) j :=
  ((finiteOpenAdjunction l E b j n).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
    (proEtaleConstantRingPullback (R l E n) j).rightDerivedFunctorIsoMapDerivedCategory

/-- The finite open projection arrow is the finite unit transpose, using the same
normalized pullback/tensor comparison. It is constructed before comparing with the
open tower arrow. The occurrence of openEvaluation changes only the j_! coordinates.
Source: blueprint paragraph (3), finite open projection map
(blueprint: lem-sp-tower-compact-support-projection-formula). -/
def finiteOpenMap (b : Base l E) (o : Operations l E b)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (C : D l E U) (L : D l E T) :=
  ((levelOpenAdjunction l E b j n).homEquiv _ _).symm
    ((levelTensor l E b U n).map (Prod.mkHom
        ((levelOpenAdjunction l E b j n).unit.app ((Ev l E U n).obj C) ≫
          (proEtaleConstantRingDerivedPullback (R l E n) j).map
            ((openEvaluation l E b (o.openOp j) n).inv.app C)) (𝟙 _)) ≫
      (levelPullTensor l E b (o.geometry j) n
        ((openD l E b (o.openOp j)).obj C) L).inv ≫
      (proEtaleConstantRingDerivedPullback (R l E n) j).map
        ((levelTensor l E b T n).map
          (Prod.mkHom ((openEvaluation l E b (o.openOp j) n).hom.app C) (𝟙 _))))

section ProperEvaluation

attribute [local irreducible] realization properMap openMap source middle
  openSource levelPullTensor finiteProperMap finiteOpenMap

end ProperEvaluation

section OpenEvaluation

attribute [local irreducible] realization properMap openMap source middle
  openSource levelPullTensor finiteProperMap finiteOpenMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

end OpenEvaluation

end AlgebraicGeometry.ProEtale.SpTowerProjection
