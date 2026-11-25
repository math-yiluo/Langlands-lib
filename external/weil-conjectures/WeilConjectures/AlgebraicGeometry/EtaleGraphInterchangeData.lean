/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
public import WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube

/-! # Graph comparisons and proper/open interchange

Source: Stacks Project, more-etale.tex, Tag 0F7J, independence of choices and
comparison of diagrams A--F; the product-graph extension recorded in the blueprint
(auxiliary; not a blueprint node).

The auxiliary records only bundle the supplied diagrams. Every arrow is built from the
recorded graph maps, normalized proper/open exchange, and canonical compositors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The normalized exchange family supplied by the support and K-injective normalization.
That normalization determines the family, rather than merely its endpoints.
Source: Stacks Tag 0F7B(b), as used in the A--F calculation of Tag 0F7J
(auxiliary; not a blueprint node). -/
def etaleGraphNormalizedProperOpenExchange (A : Type (u + 1)) [CommRing A] [Finite A] :
    ProperOpenDerivedComparisonFamily A :=
  Classical.choose (α := ProperOpenDerivedComparisonFamily A)
    (Classical.choose_spec (etaleProperOpenExchangeCube A))

/-- Shrink the middle neighborhood through a supplied proper lift.
Source: Stacks Tag 0F7J, elementary presentation move in the product-graph extension
(auxiliary; not a blueprint node). -/
def EtaleGraphPresentation.shrink {X Z W : Scheme.{u}} {h : X ⟶ Z}
    (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
    [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a) :
    EtaleGraphPresentation h where
  U := W
  P := H.P
  a := a'
  e := v ≫ H.e
  p := H.p
  fac := by simpa only [← Category.assoc, fac] using H.fac

/-- The explicit inverse triangle interchange, followed by the open compositor.
The identity-top proper/open square is Cartesian; its normalized exchange, after
removing extension by the identity, is exactly the upstream triangle isomorphism.
Source: Stacks Tag 0F7J, elementary presentation move
(auxiliary; not a blueprint node). -/
def etaleGraphShrinkInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W : Scheme.{u}} {h : X ⟶ Z} (H : EtaleGraphPresentation h)
    (a' : X ⟶ W) (v : W ⟶ H.U) [IsProper a'] [IsOpenImmersion v]
    (fac : a' ≫ v = H.a) : H.functor A ≅ (H.shrink a' v fac).functor A :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A a' v H.a fac).symm
      (D((H.e)_!open[ModuleCat.{u + 1} A]) ⋙ R((H.p)_*[ModuleCat.{u + 1} A])) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R((a')_*[ModuleCat.{u + 1} A])
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) v H.e).symm R((H.p)_*[ModuleCat.{u + 1} A]))

/-- One of the two supplied proper/open diagrams; its square need only commute.
Source: Stacks Tag 0F7J, two-diagram comparison, with the proper initial factor
of the product-graph extension
(auxiliary; not a blueprint node). -/
structure EtaleGraphInterchangeDiagram {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) where
  W : Scheme.{u}
  V : Scheme.{u}
  P : Scheme.{u}
  T : Scheme.{u}
  a : X ⟶ W
  e : W ⟶ V
  r : V ⟶ Y
  k : V ⟶ P
  p : P ⟶ T
  i : Y ⟶ T
  q : T ⟶ Z
  [properA : IsProper a]
  [properR : IsProper r]
  [properP : IsProper p]
  [properQ : IsProper q]
  [openE : IsOpenImmersion e]
  [openK : IsOpenImmersion k]
  [openI : IsOpenImmersion i]
  facF : a ≫ e ≫ r = f
  facG : i ≫ q = g
  square : CommSq k r p i

attribute [instance] EtaleGraphInterchangeDiagram.properA EtaleGraphInterchangeDiagram.properR
  EtaleGraphInterchangeDiagram.properP EtaleGraphInterchangeDiagram.properQ
  EtaleGraphInterchangeDiagram.openE EtaleGraphInterchangeDiagram.openK
  EtaleGraphInterchangeDiagram.openI

/-- The supplied presentation `t = (a,e,r)` of `f`.
Source: Stacks Tag 0F7J, two-diagram comparison
(auxiliary; not a blueprint node). -/
def EtaleGraphInterchangeDiagram.sourcePresentation {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (d : EtaleGraphInterchangeDiagram f g) :
    EtaleGraphPresentation f where
  U := d.W
  P := d.V
  a := d.a
  e := d.e
  p := d.r
  fac := d.facF

/-- The supplied open-then-proper factorization `(i,q)` of `g`.
Source: Stacks Tag 0F7J, two-diagram comparison
(auxiliary; not a blueprint node). -/
def EtaleGraphInterchangeDiagram.compactification {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (d : EtaleGraphInterchangeDiagram f g) :
    Compactification g where
  Z := d.T
  i := d.i
  g := d.q
  comm := d.facG.symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The supplied presentation `s = (a,ke,qp)` of the composite.
Source: Stacks Tag 0F7J, two-diagram comparison
(auxiliary; not a blueprint node). -/
def EtaleGraphInterchangeDiagram.compositePresentation {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (d : EtaleGraphInterchangeDiagram f g) :
    EtaleGraphPresentation (f ≫ g) where
  U := d.W
  P := d.P
  a := d.a
  e := d.e ≫ d.k
  p := d.p ≫ d.q
  fac := by
    calc
      _ = d.a ≫ d.e ≫ (d.k ≫ d.p) ≫ d.q := by simp only [Category.assoc]
      _ = d.a ≫ d.e ≫ (d.r ≫ d.i) ≫ d.q := by rw [d.square.w]
      _ = (d.a ≫ d.e ≫ d.r) ≫ (d.i ≫ d.q) := by simp only [Category.assoc]
      _ = f ≫ g := congrArg₂ (fun l m ↦ l ≫ m) d.facF d.facG

/-- The specified word `Rq Γ_Q Je Ra`, including the identity-direct-image normalization,
open compositor and proper compositor. No isomorphism with bare endpoints is chosen.
Source: Stacks Tag 0F7J, first paragraph and A--F comparison
(auxiliary; not a blueprint node). -/
def etaleGraphDiagramInterchange (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : EtaleGraphInterchangeDiagram f g) :
    d.sourcePresentation.functor A ⋙
        (EtaleGraphPresentation.ofCompactification d.compactification).functor A ≅
      d.compositePresentation.functor A :=
  Functor.isoWhiskerLeft (d.sourcePresentation.functor A)
      (etaleGraphOpenNormalization A d.compactification) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R((d.a)_*[ModuleCat.{u + 1} A])
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft D((d.e)_!open[ModuleCat.{u + 1} A])
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              (etaleGraphNormalizedProperOpenExchange A d.k d.r d.p d.i d.square)
              R((d.q)_*[ModuleCat.{u + 1} A]) ≪≫
            Functor.associator _ _ _) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) d.e d.k).symm
          (R((d.p)_*[ModuleCat.{u + 1} A]) ⋙ R((d.q)_*[ModuleCat.{u + 1} A])) ≪≫
        Functor.isoWhiskerLeft D((d.e ≫ d.k)_!open[ModuleCat.{u + 1} A])
          (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) d.p d.q))

end AlgebraicGeometry.Etale
