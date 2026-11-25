/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassDiagonal

/-! # Pullback of canonical tower classes

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Base change of a pro-etale chart along a morphism.
Source: the recorded pro-etale site (blueprint: def-sp-tower-class-pullback). -/
abbrev chart {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.ProEtᵒᵖ) :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj U

/-- Restriction of roots along the actual global-sections ring map on a pulled-back
chart. This defines the canonical map, including on the empty chart.
Source: classes (2)--(4), roots base change (blueprint: def-sp-tower-class-pullback). -/
def restrictRoot {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (n + 1))).obj.obj U) :
    (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))).obj.obj (chart f U) :=
  (Scheme.proEtaleRootsOfUnitySections X (l ^ (n + 1)) (chart f U)).symm
    (Additive.ofMul
      (restrictRootsOfUnity
        (Scheme.Γ.map (pullback.fst U.unop.hom f).op).hom (l ^ (n + 1))
          (Additive.toMul (Scheme.proEtaleRootsOfUnitySections Y (l ^ (n + 1)) U z))))

/-- The ordinary adjoint before evaluating on sections.
Source: classes (3)--(4), tower adjunction (blueprint: def-sp-tower-class-pullback). -/
def ordinaryAdjoint {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) : M ⟶ g.push.obj N :=
  (g.ordinaryAdjunction.homEquiv M N) h

-- Evaluating the fixed tower adjunction unfolds both section realizations.
/-- Evaluate the normalized ordinary adjoint as a map of finite module sheaves.
Source: classes (3)--(4), tower adjunction (blueprint: def-sp-tower-class-pullback). -/
def evaluatedAdjoint {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) (n : ℕ) :=
  (SpTowerShriek.ev l E Y n).map (ordinaryAdjoint l E g h) ≫
    (g.ordinaryPushEvaluation n).hom.app N

-- The two canonical finite sheaf realizations share their section carrier.
/-- The canonical ordinary adjoint evaluated on one finite chart. The dependency's
pushforward realization retains exactly these section carriers.
Source: classes (3)--(4), tower adjunction (blueprint: def-sp-tower-class-pullback). -/
def adjointSection {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E Y n).obj M).val.obj U) :=
  (evaluatedAdjoint l E g h n).val.app U x

-- Elaborate the fixed section formula through both finite Tate-line comparisons.
/-- Pullback of the actual Tate line. Its ordinary adjoint is fixed on all finite
pure tensors by the quotient-ring map and the root restriction above.
Source: classes (4), canonical twist transport
(blueprint: def-sp-tower-class-pullback). -/
structure LinePullback {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X) where
  iso : g.pull.obj (lineModule l E cY) ≅ lineModule l E cX
  normalization : ∀ (n : ℕ) (U : Y.ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E Y n).obj.obj U)
    (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (n + 1))).obj.obj U),
    ((proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).map
      (lineEvaluation l E cX n).hom).val.app U
        (adjointSection l E g iso.hom n U
          ((lineEvaluation l E cY n).inv.val.app U
            (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
              U.unop a z))) =
      Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
        (chart f U).unop
        ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1}
          (CommRingCat.of (FiniteRing l E n))).hom.app U a)
        (restrictRoot l f n U z)

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
