/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation

/-! # The proper maps between two product-graph models

Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D, applied to the explicit
product and supporting neighborhoods of the graph model.
(auxiliary; not a blueprint node).

Every map below is a pullback lift. The two transport isomorphisms are made from
Cartesian proper/open exchange and the canonical direct-image compositors.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Transport a proper/open/proper word along a Cartesian proper ambient map.
Source: Stacks Tag 0F7C, vertical proper/open pasting
(auxiliary; not a blueprint node). -/
def etaleProperAmbientTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U U' P P' : Scheme.{u}}
    (a : X ⟶ U) (e : U ⟶ P) (p : P ⟶ Y)
    (a' : X ⟶ U') (e' : U' ⟶ P') (p' : P' ⟶ Y)
    [IsOpenImmersion e] [IsOpenImmersion e']
    (r : P' ⟶ P) [IsProper r] (q : U' ⟶ U)
    (sq : IsPullback q e' e r) (ha : a' ≫ q = a) (hp : r ≫ p = p') :
    R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ⋙
        R((p)_*[ModuleCat.{u + 1} A]) ≅
      R((a')_*[ModuleCat.{u + 1} A]) ⋙ D((e')_!open[ModuleCat.{u + 1} A]) ⋙
        R((p')_*[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) a' q a ha).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A sq) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) r p p' hp))

namespace EtaleGraphPresentation

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (s t : EtaleGraphPresentation f) (pr : t.P ⟶ s.P) [IsProper pr]
  (q : t.U ⟶ s.U) (sq : IsPullback q t.e s.e pr)
  (hz : t.a ≫ q = s.a) (hp : pr ≫ s.p = t.p)

/-- The map `P_t ×_Y C → P_s ×_Y C` induced by the proper ambient map.
Source: Stacks Tags 0F7C--0F7D, proper-projection grid
(auxiliary; not a blueprint node). -/
def properAmbientProduct : pullback t.p c.g ⟶ pullback s.p c.g :=
  pullback.lift (pullback.fst t.p c.g ≫ pr) (pullback.snd t.p c.g)
    (by rw [Category.assoc, hp]; exact pullback.condition)

omit [IsProper pr] in
/-- The product map is Cartesian over the ambient map.
Source: Stacks Tags 0F7C--0F7D; cancel the defining right pullback square
(auxiliary; not a blueprint node). -/
theorem properAmbientProduct_isPullback :
    IsPullback (s.properAmbientProduct c t pr hp) (pullback.fst t.p c.g)
      (pullback.fst s.p c.g) pr := by
  apply IsPullback.of_right (h₁₂ := pullback.snd s.p c.g)
    (h₂₂ := s.p) (v₁₃ := c.g)
  · simpa only [properAmbientProduct, pullback.lift_snd, hp] using
      (IsPullback.of_hasPullback t.p c.g).flip
  · simp only [properAmbientProduct, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback s.p c.g).flip

/-- Properness of the product map follows by base change of `pr`.
Source: Stacks Tags 0F7C--0F7D
(auxiliary; not a blueprint node). -/
instance properAmbientProduct_proper : IsProper (s.properAmbientProduct c t pr hp) :=
  MorphismProperty.of_isPullback (s.properAmbientProduct_isPullback c t pr hp).flip
    inferInstance

omit [IsProper pr] in
/-- The product map commutes with the proper maps to the base.
Source: the first pullback projection equation
(auxiliary; not a blueprint node). -/
theorem properAmbientProduct_base :
    s.properAmbientProduct c t pr hp ≫ (pullback.fst s.p c.g ≫ s.p) =
      pullback.fst t.p c.g ≫ t.p := by
  dsimp only [properAmbientProduct]
  rw [pullback.lift_fst_assoc, Category.assoc, hp]

/-- The map on the neighborhood pulled back from the compactification open.
Source: Stacks Tags 0F7C--0F7D, first supporting neighborhood
(auxiliary; not a blueprint node). -/
def properAmbientFirst :
    pullback (pullback.snd t.p c.g) c.i ⟶ pullback (pullback.snd s.p c.g) c.i :=
  pullback.lift (pullback.fst _ _ ≫ s.properAmbientProduct c t pr hp) (pullback.snd _ _)
    (by simp only [Category.assoc, properAmbientProduct, pullback.lift_snd];
        exact pullback.condition)

omit [IsProper pr] in
/-- The first supporting neighborhood square is Cartesian.
Source: pull back the proper product map along the open from the compactification
(auxiliary; not a blueprint node). -/
theorem properAmbientFirst_isPullback :
    IsPullback (s.properAmbientFirst c t pr hp) (pullback.fst _ _)
      (pullback.fst _ _) (s.properAmbientProduct c t pr hp) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd (pullback.snd s.p c.g) c.i)
    (h₂₂ := pullback.snd s.p c.g) (v₁₃ := c.i)
  · simpa only [properAmbientFirst, properAmbientProduct, pullback.lift_snd] using
      (IsPullback.of_hasPullback (pullback.snd t.p c.g) c.i).flip
  · simp only [properAmbientFirst, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback (pullback.snd s.p c.g) c.i).flip

/-- The map on the neighborhood pulled back from the presentation open.
Source: Stacks Tags 0F7C--0F7D, second supporting neighborhood
(auxiliary; not a blueprint node). -/
def properAmbientSecond :
    pullback (pullback.fst t.p c.g) t.e ⟶ pullback (pullback.fst s.p c.g) s.e :=
  pullback.lift (pullback.fst _ _ ≫ s.properAmbientProduct c t pr hp)
    (pullback.snd _ _ ≫ q) (by
      simp only [Category.assoc, properAmbientProduct, pullback.lift_fst]
      rw [← Category.assoc, pullback.condition, Category.assoc, ← sq.w])

omit [IsProper pr] in
/-- The second supporting neighborhood square is Cartesian.
Source: paste the two defining neighborhood squares with the supplied Cartesian open square
(auxiliary; not a blueprint node). -/
theorem properAmbientSecond_isPullback :
    IsPullback (s.properAmbientSecond c t pr q sq hp) (pullback.fst _ _)
      (pullback.fst _ _) (s.properAmbientProduct c t pr hp) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd (pullback.fst s.p c.g) s.e)
    (h₂₂ := pullback.fst s.p c.g) (v₁₃ := s.e)
  · simpa only [properAmbientSecond, properAmbientProduct, pullback.lift_snd,
      pullback.lift_fst] using
      ((IsPullback.of_hasPullback (pullback.fst t.p c.g) t.e).flip.paste_horiz sq)
  · simp only [properAmbientSecond, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback (pullback.fst s.p c.g) s.e).flip

include sq hz in
omit [IsProper pr] in
/-- The first graph lift commutes with the first neighborhood map.
Source: compare both pullback projections, using the ambient square and `hz`
(auxiliary; not a blueprint node). -/
theorem properAmbientFirst_graph :
    locallyClosedGraphS₁ t.a t.e t.p c.i c.g
        ((Category.assoc _ _ _).trans (t.fac.trans c.comm)) ≫
      s.properAmbientFirst c t pr hp =
    locallyClosedGraphS₁ s.a s.e s.p c.i c.g
      ((Category.assoc _ _ _).trans (s.fac.trans c.comm)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, properAmbientFirst]
    apply pullback.hom_ext
    · simp only [Category.assoc, properAmbientProduct, locallyClosedGraphS₁,
        locallyClosedGraphV, pullback.lift_fst_assoc, pullback.lift_fst]
      rw [← sq.w, ← Category.assoc, hz]
    · simp only [Category.assoc, properAmbientProduct, locallyClosedGraphS₁,
        locallyClosedGraphV, pullback.lift_fst_assoc,
        pullback.lift_snd]
  · simp only [properAmbientFirst, Category.assoc, pullback.lift_snd, locallyClosedGraphS₁]

include hz in
omit [IsProper pr] in
/-- The second graph lift commutes with the second neighborhood map.
Source: compare both pullback projections and use `t.a ≫ q = s.a`
(auxiliary; not a blueprint node). -/
theorem properAmbientSecond_graph :
    locallyClosedGraphS₂ t.a t.e t.p c.i c.g
        ((Category.assoc _ _ _).trans (t.fac.trans c.comm)) ≫
      s.properAmbientSecond c t pr q sq hp =
    locallyClosedGraphS₂ s.a s.e s.p c.i c.g
      ((Category.assoc _ _ _).trans (s.fac.trans c.comm)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, properAmbientSecond]
    apply pullback.hom_ext
    · simp only [Category.assoc, properAmbientProduct, locallyClosedGraphS₂,
        locallyClosedGraphV, pullback.lift_fst_assoc, pullback.lift_fst]
      rw [← sq.w, ← Category.assoc, hz]
    · simp only [Category.assoc, properAmbientProduct, locallyClosedGraphS₂,
        locallyClosedGraphV, pullback.lift_fst_assoc,
        pullback.lift_snd]
  · simp only [properAmbientSecond, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, locallyClosedGraphS₂, hz]

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The specified transport on the first graph word.
Source: Stacks Tag 0F7C, proper projection exchange for the first supporting open
(auxiliary; not a blueprint node). -/
def properAmbientFirstTransport :
    R((locallyClosedGraphS₁ s.a s.e s.p c.i c.g
      ((Category.assoc _ _ _).trans (s.fac.trans c.comm)))_*[ModuleCat.{u + 1} A]) ⋙
        D((pullback.fst (pullback.snd s.p c.g) c.i)_!open[ModuleCat.{u + 1} A]) ⋙
        R((pullback.fst s.p c.g ≫ s.p)_*[ModuleCat.{u + 1} A]) ≅
    R((locallyClosedGraphS₁ t.a t.e t.p c.i c.g
      ((Category.assoc _ _ _).trans (t.fac.trans c.comm)))_*[ModuleCat.{u + 1} A]) ⋙
        D((pullback.fst (pullback.snd t.p c.g) c.i)_!open[ModuleCat.{u + 1} A]) ⋙
        R((pullback.fst t.p c.g ≫ t.p)_*[ModuleCat.{u + 1} A]) :=
  etaleProperAmbientTransport A _ _ _ _ _ _ (s.properAmbientProduct c t pr hp)
    (s.properAmbientFirst c t pr hp) (s.properAmbientFirst_isPullback c t pr hp)
    (s.properAmbientFirst_graph c t pr q sq hz hp) (s.properAmbientProduct_base c t pr hp)

/-- The specified transport on the second graph word.
Source: Stacks Tag 0F7C, proper projection exchange for the second supporting open
(auxiliary; not a blueprint node). -/
def properAmbientSecondTransport :
    R((locallyClosedGraphS₂ s.a s.e s.p c.i c.g
      ((Category.assoc _ _ _).trans (s.fac.trans c.comm)))_*[ModuleCat.{u + 1} A]) ⋙
        D((pullback.fst (pullback.fst s.p c.g) s.e)_!open[ModuleCat.{u + 1} A]) ⋙
        R((pullback.fst s.p c.g ≫ s.p)_*[ModuleCat.{u + 1} A]) ≅
    R((locallyClosedGraphS₂ t.a t.e t.p c.i c.g
      ((Category.assoc _ _ _).trans (t.fac.trans c.comm)))_*[ModuleCat.{u + 1} A]) ⋙
        D((pullback.fst (pullback.fst t.p c.g) t.e)_!open[ModuleCat.{u + 1} A]) ⋙
        R((pullback.fst t.p c.g ≫ t.p)_*[ModuleCat.{u + 1} A]) :=
  etaleProperAmbientTransport A _ _ _ _ _ _ (s.properAmbientProduct c t pr hp)
    (s.properAmbientSecond c t pr q sq hp) (s.properAmbientSecond_isPullback c t pr q sq hp)
    (s.properAmbientSecond_graph c t pr q sq hz hp) (s.properAmbientProduct_base c t pr hp)

end EtaleGraphPresentation

end AlgebraicGeometry.Etale
