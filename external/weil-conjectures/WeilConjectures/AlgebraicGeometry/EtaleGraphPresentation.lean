/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.EtaleLocallyClosedGraphModel

/-! # Proper/open/proper presentations and their specified graph maps

Source: Stacks Project, Tags 0F7B--0F7F; the explicit graph formula in
`EtaleLocallyClosedGraphModel.lean`.
(auxiliary; not a blueprint node).

These definitions are moved unchanged from `EtaleGraphComparisonBaseChange` so that
individual coherence lemmas can refer to the same maps without an import cycle.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- A supplied presentation `f = p e a`, with proper outer factors and open middle factor.
Source: the presentations in the product-graph argument, Stacks Tags 0F7C--0F7F
(auxiliary; not a blueprint node). -/
structure EtaleGraphPresentation {X Y : Scheme.{u}} (f : X ⟶ Y) where
  U : Scheme.{u}
  P : Scheme.{u}
  a : X ⟶ U
  e : U ⟶ P
  p : P ⟶ Y
  [properA : IsProper a]
  [openE : IsOpenImmersion e]
  [properP : IsProper p]
  fac : a ≫ e ≫ p = f

attribute [instance] EtaleGraphPresentation.properA EtaleGraphPresentation.openE
  EtaleGraphPresentation.properP

/-- An open-then-proper factorization is the presentation with identity first factor.
Source: `LowerShriekComposition.lean`, graph-model source
(auxiliary; not a blueprint node). -/
def EtaleGraphPresentation.ofCompactification {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : EtaleGraphPresentation f where
  U := X
  P := c.Z
  a := 𝟙 X
  e := c.i
  p := c.g
  fac := by simpa using c.comm.symm

/-- The actual ordinary unbounded functor `Rp_* De_! Ra_*` attached to a presentation.
Source: `LowerShriekComposition.lean`, target of the graph comparison
(auxiliary; not a blueprint node). -/
def EtaleGraphPresentation.functor (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f) :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A Y :=
  R((t.a)_*[ModuleCat.{u + 1} A]) ⋙ D((t.e)_!open[ModuleCat.{u + 1} A]) ⋙
    R((t.p)_*[ModuleCat.{u + 1} A])

/-- Remove the identity proper direct image in an open-then-proper presentation.
Source: `LowerShriekComposition.lean`, `rightDerivedLowerStarIdIso`
(auxiliary; not a blueprint node). -/
def etaleGraphOpenNormalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (EtaleGraphPresentation.ofCompactification c).functor A ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Functor.isoWhiskerRight (rightDerivedLowerStarIdIso A X) _ ≪≫ Functor.leftUnitor _

/-- The specified `B_{t,c}`: use the graph theorem only for its properness proofs and
then evaluate its explicit `B₁`, intersection `B₁₂`, and inverse `B₂` composite. No
endpoint isomorphism is chosen. Source: `EtaleLocallyClosedGraphModel.lean`, graph formula
(auxiliary; not a blueprint node). -/
def etaleGraphComparisonFromOpen (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (t : EtaleGraphPresentation f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅ t.functor A :=
  let model := Classical.choice
    (etaleLocallyClosedGraphModel A t.a t.e t.p c.i c.g c.comm.symm t.fac)
  letI := model.properS₁
  letI := model.properS₂
  locallyClosedGraphIso t.a t.e t.p c.i c.g
    ((Category.assoc t.a t.e t.p).trans (t.fac.trans c.comm)) A

/-- `C_{t,s} = B_{t,c} B_{s,c}^{-1}`, retaining the auxiliary compactification explicitly
until the independence theorem. Source: Stacks Tags 0F7C--0F7D, product/intersection argument
(auxiliary; not a blueprint node). -/
def etaleGraphComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) : s.functor A ≅ t.functor A :=
  (etaleGraphComparisonFromOpen A c s).symm ≪≫ etaleGraphComparisonFromOpen A c t

/-- Cartesian representatives of the three pulled-back factors of a presentation.
The maps `v` and `b` are the source and base projections. Source: Stacks Tag 0F7F
(auxiliary; not a blueprint node). -/
structure EtaleGraphPresentation.BaseChange
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (t : EtaleGraphPresentation f) (t' : EtaleGraphPresentation f')
    (v : X' ⟶ X) (b : Y' ⟶ Y) where
  u : t'.U ⟶ t.U
  w : t'.P ⟶ t.P
  aSquare : IsPullback v t'.a t.a u
  eSquare : IsPullback u t'.e t.e w
  pSquare : IsPullback w t'.p t.p b

/-- The Cartesian representatives for the base change of an open-then-proper presentation.
Source: `Compactification.BaseChange`, the two constituent pullback squares
(auxiliary; not a blueprint node). -/
def EtaleGraphPresentation.ofCompactificationBaseChange
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} (c : Compactification f) (sq : IsPullback v f' f b) :
    (EtaleGraphPresentation.ofCompactification c).BaseChange
      (EtaleGraphPresentation.ofCompactification (c.ofIsPullback sq)) v b where
  u := v
  w := pullback.fst c.g b
  aSquare := IsPullback.id_vert v
  eSquare := c.isPullback_i_ofIsPullback sq
  pSquare := (c.isPullback_g_ofIsPullback sq).flip

/-- The actual successive canonical exchanges `chi_t`: proper exchange for `p`, inverse
of the unit-normalized open mate for `e`, then proper exchange for `a`, with associators.
Source: Stacks Tag 0F7F; `exactDerivedBaseChangeMap` and the termwise open-unit mate
(auxiliary; not a blueprint node). -/
def etaleGraphPresentationExchange (A : Type (u + 1)) [CommRing A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {t : EtaleGraphPresentation f} {t' : EtaleGraphPresentation f'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} (d : t.BaseChange t' v b) :
    t.functor A ⋙ D((b)^*[ModuleCat.{u + 1} A]) ⟶
      D((v)^*[ModuleCat.{u + 1} A]) ⋙ t'.functor A :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) d.pSquare.toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) d.eSquare).inv _ ≫
      (Functor.associator _ _ _).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) d.aSquare.toCommSq) _ ≫
    (Functor.associator _ _ _).hom

end AlgebraicGeometry.Etale
