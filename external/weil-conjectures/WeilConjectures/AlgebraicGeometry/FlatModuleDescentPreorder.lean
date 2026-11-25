/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.FlatModuleDescentPreorderStage
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.PullbackModelFlatnessComparison

/-! # Flat-module descent over a directed preorder

Source: Stacks Project, Tags 05LY, 0032, 01U8, 01JX and 0097.
(blueprint: lem-pc-flat-module-descent-preorder).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Relative flatness of a fixed finitely presented module descends over a directed preorder.

Source: Stacks Project, limits.tex, Tag 05LY (lemma-descend-module-flat-finite-presentation);
categories.tex, Tag 0032 (lemma-directed-category-system); morphisms.tex, Tag 01U8
(lemma-base-change-module-flat); schemes.tex, Tag 01JX; sheaves.tex, Tag 0097.
(blueprint: lem-pc-flat-module-descent-preorder).

Proof: The object i makes the directed preorder nonempty, hence its thin category is
filtered. Tag 0032 gives a final functor from a nonempty directed partial order J.
Choose an object of J with a morphism from i to its image using finality, and pull M
back to that stage. Restrict the ring diagram and the spectrum cone along the final
functor; its opposite is initial, so the restricted cone is still limiting. Tensor
pullback composition and cartesian pasting identify the limit pullback of this module
with the original limit pullback, hence it is flat. Apply partial-order flat descent
(Tag 05LY) to this fixed pulled-back module. Its eventual stage maps to a stage j of I
above i. For every k above j in I, cartesian base change preserves relative flatness
(Tag 01U8); tensor-pullback composition identifies the result with the direct pullback
of M from i to k. A cartesian-model comparison transfers relative flatness
from the canonical pullback to any given cartesian square: the unique comparison
isomorphism preserves the base projection and identifies section modules on affine
opens as modules over the same base ring. Apply this both at the limit and at k.
Thus k need not be in the image of J. Zero modules and empty source
schemes remain flat, and i excludes an empty index category; no antisymmetry or
flatness of the transition maps is used. -/
theorem exists_eventually_isFlatOver_of_isPullback_limit_preorder
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : Xi.Modules) [M.IsFinitePresentation]
    {X : Scheme.{u}} (a : X ⟶ Xi) (b : X ⟶ c.pt)
    (hcart : IsPullback a b f (c.π.app (op i)))
    (hflat : ((Scheme.Modules.tensorPullback a).obj M).IsFlatOver b) :
    ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hjk : j ≤ k)
      {Y : Scheme.{u}} (p : Y ⟶ Xi) (q : Y ⟶ Spec (R.obj k)),
      IsPullback p q f (Spec.map (R.map (homOfLE (hij.trans hjk)))) →
      ((Scheme.Modules.tensorPullback p).obj M).IsFlatOver q := by
  let ac := pullback.fst f (c.π.app (op i))
  let bc := pullback.snd f (c.π.app (op i))
  have hcanon : ((Scheme.Modules.tensorPullback ac).obj M).IsFlatOver bc := by
    exact (isFlatOver_tensorPullback_iff_of_isPullback hcart
      (IsPullback.of_hasPullback f (c.π.app (op i))) M).mp hflat
  obtain ⟨j, hij, hj⟩ :=
    exists_isFlatOver_of_isPullback_limit_preorder_stage R c hc i f M hcanon
  refine ⟨j, hij, ?_⟩
  intro k hjk Y p q hq
  let gj := Spec.map (R.map (homOfLE hij))
  let gk := Spec.map (R.map (homOfLE (hij.trans hjk)))
  let t := Spec.map (R.map (homOfLE hjk))
  let aj := pullback.fst f gj
  let bj := pullback.snd f gj
  let N := (Scheme.Modules.tensorPullback aj).obj M
  have : N.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_tensorPullback aj M
  have hN : N.IsFlatOver bj := hj
  have hbase := relativelyFlat_module_pullback bj t N hN
  let d := pullback.fst bj t
  let e := pullback.snd bj t
  have hpaste : IsPullback (d ≫ aj) e f gk := by
    have h := (IsPullback.of_hasPullback bj t).paste_horiz
      (IsPullback.of_hasPullback f gj)
    simpa [d, e, aj, bj, gj, gk, t, ← Spec.map_comp, ← R.map_comp] using h
  obtain ⟨δ⟩ := Scheme.Modules.nonempty_tensorPullbackComp d aj
  have hcomp : ((Scheme.Modules.tensorPullback (d ≫ aj)).obj M).IsFlatOver e :=
    hbase.of_iso (δ.app M).symm
  exact (isFlatOver_tensorPullback_iff_of_isPullback hpaste hq M).mp hcomp

end AlgebraicGeometry
