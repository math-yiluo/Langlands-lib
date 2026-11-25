/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTwisting

/-! # Projective for canonical tower classes

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-projective).
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

/-- The geometric data used by the projective-line splitting. All functors are the
recorded proper tower direct image and its geometric inverse-image adjunction.
Source: classes (4) (blueprint: def-sp-tower-class-projective). -/
structure Projective (b : SpTowerShriek.Base l E) (S : Scheme.{u})
    (cS : Chern l E S) (cP : Chern l E (ProjectiveLine S))
    (tS : Twisting l E cS) (tP : Twisting l E cP) where
  geometry : SpTowerShriek.Geometry l E b (ProjectiveLine S ↘ S)
  coefficientPullback : CoefficientPullback l E b (ProjectiveLine S ↘ S) geometry
  linePullback : LinePullback l E (ProjectiveLine S ↘ S) geometry cS cP
  positivePullback : PositivePullback l E (ProjectiveLine S ↘ S) geometry tS tP linePullback
  /-- Projection for a line is invertible, with its canonical mate map. -/
  projection_iso : IsIso (projection l E geometry positivePullback
    (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))

attribute [instance] Projective.projection_iso

/-- Twisting and shifting Rq_* of the coefficient unit: the projection mate, the
ordinary Tate-line identification, and the derived shift comparison in that order.
Source: classes (4), trace definition (blueprint: def-sp-tower-class-projective). -/
def Projective.twistedPush {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {cS : Chern l E S} {cP : Chern l E (ProjectiveLine S)}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Projective l E b S cS cP tS tP) :
    ((tS.T l E).obj ((SpTowerShriek.push l E b p.geometry).obj
      (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))))⟦(2 : ℤ)⟧ ≅
    (SpTowerShriek.push l E b p.geometry).obj ((line l E cP)⟦(2 : ℤ)⟧) :=
  (shiftFunctor _ (2 : ℤ)).mapIso
    (asIso (projection l E p.geometry p.positivePullback
      (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))) ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((SpTowerShriek.push l E b p.geometry).mapIso (tP.positiveUnit l E)) ≪≫
    ((SpTowerShriek.push l E b p.geometry).commShiftIso (2 : ℤ)).symm.app (line l E cP)

/-- The adjoint of c1(O_P(1)), using the actual coefficient pullback unit.
Source: classes (4) (blueprint: def-sp-tower-class-projective). -/
def Projective.chernAdjoint {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {cS : Chern l E S} {cP : Chern l E (ProjectiveLine S)}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Projective l E b S cS cP tS tP) :
    unit S (Arings l E S) ⟶
      (SpTowerShriek.push l E b p.geometry).obj ((line l E cP)⟦(2 : ℤ)⟧) :=
  (SpTowerShriek.adjunction l E b p.geometry).homEquiv _ _
    ((p.coefficientPullback.derivedIso l E).hom ≫
      firstChern l E cP (hyperplanePic S))

/-- Cancellation of positive twisting followed by negative twisting, obtained by
localizing the specified ordinary tensor/Hom unit isomorphism.
Source: classes (4), untwisting the Chern arrow (blueprint: def-sp-tower-class-projective). -/
def Twisting.cancelNegative {T : Scheme.{u}} {c : Chern l E T} (t : Twisting l E c) :
    t.T l E ⋙ t.N l E ≅ 𝟭 (D T (Arings l E T)) :=
  Functor.mapDerivedCategoryCompIso t.equivalence.functor t.equivalence.inverse ≪≫
    Functor.mapDerivedCategoryNatIso t.equivalence.unitIso.symm ≪≫
    Functor.mapDerivedCategoryIdIso (Systems T (Arings l E T))

/-- The second summand is obtained by untwisting the actual adjoint Chern class.
The inverse tensor/Hom adjunction and shift cancellation specify its orientation;
it is not a free morphism whose finite components alone are prescribed.
Source: classes (4), construction of b_q (blueprint: def-sp-tower-class-projective). -/
def Projective.second {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {cS : Chern l E S} {cP : Chern l E (ProjectiveLine S)}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Projective l E b S cS cP tS tP) :
    (inverseLine l E cS)⟦(-2 : ℤ)⟧ ⟶
      (SpTowerShriek.push l E b p.geometry).obj
        (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) :=
  ((tS.inverseUnit l E).inv ≫
    (tS.N l E).map
      (p.chernAdjoint l E ≫ (p.twistedPush l E).inv ≫
        ((tS.T l E).commShiftIso (2 : ℤ)).inv.app
          ((SpTowerShriek.push l E b p.geometry).obj
            (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))) ≫
    (tS.cancelNegative l E).hom.app
      (((SpTowerShriek.push l E b p.geometry).obj
        (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ))⟦(2 : ℤ)⟧))⟦(-2 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (D S (Arings l E S)) (2 : ℤ) (-2) (by decide)).hom.app
      ((SpTowerShriek.push l E b p.geometry).obj
        (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))

/-- The specified b_q is the biproduct map with the unit first and the untwisted
Chern class second.
Source: classes (4) (blueprint: def-sp-tower-class-projective). -/
def Projective.bq {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {cS : Chern l E S} {cP : Chern l E (ProjectiveLine S)}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Projective l E b S cS cP tS tP) :
    (unit S (Arings l E S)) ⊞ (inverseLine l E cS)⟦(-2 : ℤ)⟧ ⟶
      (SpTowerShriek.push l E b p.geometry).obj
        (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) :=
  biprod.desc (unitArrow l E p.coefficientPullback) (p.second l E)

/-- The trace is literally positive twisting and shifting of b_q inverse,
followed by its second projection and the canonical dual-line evaluation.
Source: classes (4), trace normalization (blueprint: def-sp-tower-class-projective). -/
def Projective.trace {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {cS : Chern l E S} {cP : Chern l E (ProjectiveLine S)}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Projective l E b S cS cP tS tP) [IsIso (p.bq l E)] :
    (SpTowerShriek.push l E b p.geometry).obj ((line l E cP)⟦(2 : ℤ)⟧) ⟶
      unit S (Arings l E S) :=
  (p.twistedPush l E).inv ≫
    ((tS.T l E).map (inv (p.bq l E)))⟦(2 : ℤ)⟧' ≫
    ((tS.T l E).map (biprod.snd :
      (unit S (Arings l E S)) ⊞ (inverseLine l E cS)⟦(-2 : ℤ)⟧ ⟶
        (inverseLine l E cS)⟦(-2 : ℤ)⟧))⟦(2 : ℤ)⟧' ≫
    (((tS.T l E).commShiftIso (-2 : ℤ)).hom.app (inverseLine l E cS))⟦(2 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (D S (Arings l E S)) (-2 : ℤ) 2 (by decide)).hom.app
      ((tS.T l E).obj (inverseLine l E cS)) ≫ (tS.contract l E).hom

/-- The exact ordinary Tate-line pullback, localized and shifted by two.
Source: classes (4) (blueprint: def-sp-tower-class-projective). -/
def LinePullback.derivedIso {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {g : SpTowerShriek.Geometry l E b f}
    {cY : Chern l E Y} {cX : Chern l E X} (p : LinePullback l E f g cY cX) :
    (SpTowerShriek.pull l E b g).obj (line l E cY) ≅ line l E cX :=
  (g.pull.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso p.iso

/-- The unit component of the twisted projective-line decomposition.
Source: classes (4), finite trace normalization (blueprint: def-sp-tower-class-projective). -/
def Projective.twistedUnit {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {cS : Chern l E S} {cP : Chern l E (ProjectiveLine S)}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Projective l E b S cS cP tS tP) :
    (line l E cS)⟦(2 : ℤ)⟧ ⟶
      (SpTowerShriek.push l E b p.geometry).obj ((line l E cP)⟦(2 : ℤ)⟧) :=
  (SpTowerShriek.adjunction l E b p.geometry).unit.app _ ≫
    (SpTowerShriek.push l E b p.geometry).map
      (((SpTowerShriek.pull l E b p.geometry).commShiftIso (2 : ℤ)).hom.app _ ≫
        ((p.linePullback.derivedIso l E).hom)⟦(2 : ℤ)⟧')

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
