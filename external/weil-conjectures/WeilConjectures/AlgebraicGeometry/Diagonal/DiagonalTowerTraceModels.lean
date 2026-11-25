/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology

/-!
# The completed projective-line trace and the diagonal integrals

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-trace.md (blueprint: def-sfb-diagonal-trace-models).

The strict systems have discrete constant Z_l coefficients. The final traces have
completed coefficients. The localization choices below only package the size data.

## Main definitions
- `DiagonalTrace.Model` specifies the projective model and its unit/Chern splitting.
- `DiagonalTrace.Restriction` fixes the discrete scalar restriction on strict systems.
- `DiagonalTrace.ExactSquare` and `DiagonalTrace.LimitSquare` normalize derived comparisons.
- `diagonalTracePush`, `exactConeComparison`, and `DiagonalTrace.shiftedComparison`
  give the actual direct image, coefficient-cone map, and shifted comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w v a b c va vb vc wa wb wc

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Localization choices at one site, using the size convention of the diagonal theorem.
Source: blueprint standing coefficient convention
(blueprint: def-sfb-diagonal-trace-models). -/
class DiagonalTraceLocalizations (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) where
  ab : HasDerivedCategory.{u + 1} (DiagonalAb X)
  mod : HasDerivedCategory.{u + 1} (DiagonalMod ℓ X)
  systems : HasDerivedCategory.{u + 1} (DiagonalSystems ℓ X)
  abSystems : HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb X)
  completed : HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ X)
  completedSystems : HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ X)
  ext : HasExt.{u + 1} (DiagonalSystems ℓ X)

attribute [instance_reducible] DiagonalTraceLocalizations.ab DiagonalTraceLocalizations.mod
  DiagonalTraceLocalizations.systems DiagonalTraceLocalizations.abSystems
  DiagonalTraceLocalizations.completed DiagonalTraceLocalizations.completedSystems

attribute [instance] DiagonalTraceLocalizations.ab DiagonalTraceLocalizations.mod
  DiagonalTraceLocalizations.systems DiagonalTraceLocalizations.abSystems
  DiagonalTraceLocalizations.completed DiagonalTraceLocalizations.completedSystems
  DiagonalTraceLocalizations.ext

/-- Direct image with the action induced by the actual completed coefficient map.
Source: blueprint clause 1 (blueprint: def-sfb-diagonal-trace-models). -/
def diagonalTracePush (ℓ : ℕ) [Fact ℓ.Prime] {X S : Scheme.{u}} (f : X ⟶ S) :
    DiagonalCompleted ℓ X ⥤ DiagonalCompleted ℓ S :=
  SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (diagonalCompletedCoefficientMap ℓ f)) ⋙
    Scheme.proEtaleRingedDirectImage f (Scheme.purTwistZlCompletion S ℓ)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses WeilConjectures
open AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical geometric data on a projective-line model. All functors are the
recorded proper tower direct image and its geometric inverse-image adjunction.
Source: blueprint trace clause 1 and proof steps 1--4 (blueprint: def-sfb-diagonal-trace-models). -/
structure Model (b : SpTowerShriek.Base l E) (S X : Scheme.{u}) (f : X ⟶ S)
    (cS : Chern l E S) (cP : Chern l E X)
    (tS : Twisting l E cS) (tP : Twisting l E cP) where
  model : X ≅ ProjectiveLine S
  over_eq : model.hom ≫ (ProjectiveLine S ↘ S) = f
  geometry : SpTowerShriek.Geometry l E b f
  coefficientPullback : CoefficientPullback l E b f geometry
  linePullback : LinePullback l E f geometry cS cP
  positivePullback : PositivePullback l E f geometry tS tP linePullback
  /-- Projection for a line is invertible, with its canonical mate map. -/
  projection_iso : IsIso (projection l E geometry positivePullback
    (unit X (Arings l E X)))

attribute [instance] Model.projection_iso

/-- Twisting and shifting Rq_* of the coefficient unit: the projection mate, the
ordinary Tate-line identification, and the derived shift comparison in that order.
Source: blueprint trace clause 1 and proof steps 1--4, trace definition (blueprint:
def-sfb-diagonal-trace-models). -/
def Model.twistedPush {b : SpTowerShriek.Base l E} {S X : Scheme.{u}} {f : X ⟶ S}
    {cS : Chern l E S} {cP : Chern l E X}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Model l E b S X f cS cP tS tP) :
    ((tS.T l E).obj ((SpTowerShriek.push l E b p.geometry).obj
      (unit X (Arings l E X))))⟦(2 : ℤ)⟧ ≅
    (SpTowerShriek.push l E b p.geometry).obj ((line l E cP)⟦(2 : ℤ)⟧) :=
  (shiftFunctor _ (2 : ℤ)).mapIso
    (asIso (projection l E p.geometry p.positivePullback
      (unit X (Arings l E X)))) ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((SpTowerShriek.push l E b p.geometry).mapIso (tP.positiveUnit l E)) ≪≫
    ((SpTowerShriek.push l E b p.geometry).commShiftIso (2 : ℤ)).symm.app (line l E cP)

/-- The adjoint of c1(O_P(1)), using the actual coefficient pullback unit.
Source: blueprint trace clause 1 and proof steps 1--4 (blueprint: def-sfb-diagonal-trace-models). -/
def Model.chernAdjoint {b : SpTowerShriek.Base l E} {S X : Scheme.{u}} {f : X ⟶ S}
    {cS : Chern l E S} {cP : Chern l E X}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Model l E b S X f cS cP tS tP) :
    unit S (Arings l E S) ⟶
      (SpTowerShriek.push l E b p.geometry).obj ((line l E cP)⟦(2 : ℤ)⟧) :=
  (SpTowerShriek.adjunction l E b p.geometry).homEquiv _ _
    ((p.coefficientPullback.derivedIso l E).hom ≫
      firstChern l E cP
        (Scheme.Pic.mapHom p.model.hom (hyperplanePic S)))

/-- The second summand is obtained by untwisting the actual adjoint Chern class.
The inverse tensor/Hom adjunction and shift cancellation specify its orientation;
it is not a free morphism whose finite components alone are prescribed.
Source: blueprint trace clause 1 and proof steps 1--4, construction of b_q (blueprint:
def-sfb-diagonal-trace-models). -/
def Model.second {b : SpTowerShriek.Base l E} {S X : Scheme.{u}} {f : X ⟶ S}
    {cS : Chern l E S} {cP : Chern l E X}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Model l E b S X f cS cP tS tP) :
    (inverseLine l E cS)⟦(-2 : ℤ)⟧ ⟶
      (SpTowerShriek.push l E b p.geometry).obj
        (unit X (Arings l E X)) :=
  ((tS.inverseUnit l E).inv ≫
    (tS.N l E).map
      (p.chernAdjoint l E ≫ (p.twistedPush l E).inv ≫
        ((tS.T l E).commShiftIso (2 : ℤ)).inv.app
          ((SpTowerShriek.push l E b p.geometry).obj
            (unit X (Arings l E X)))) ≫
    (tS.cancelNegative l E).hom.app
      (((SpTowerShriek.push l E b p.geometry).obj
        (unit X (Arings l E X) ))⟦(2 : ℤ)⟧))⟦(-2 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (D S (Arings l E S)) (2 : ℤ) (-2) (by decide)).hom.app
      ((SpTowerShriek.push l E b p.geometry).obj
        (unit X (Arings l E X)))

/-- The specified b_q is the biproduct map with the unit first and the untwisted
Chern class second.
Source: blueprint trace clause 1 and proof steps 1--4 (blueprint: def-sfb-diagonal-trace-models). -/
def Model.bq {b : SpTowerShriek.Base l E} {S X : Scheme.{u}} {f : X ⟶ S}
    {cS : Chern l E S} {cP : Chern l E X}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Model l E b S X f cS cP tS tP) :
    (unit S (Arings l E S)) ⊞ (inverseLine l E cS)⟦(-2 : ℤ)⟧ ⟶
      (SpTowerShriek.push l E b p.geometry).obj
        (unit X (Arings l E X)) :=
  biprod.desc (unitArrow l E p.coefficientPullback) (p.second l E)

/-- The trace is literally positive twisting and shifting of b_q inverse,
followed by its second projection and the canonical dual-line evaluation.
Source: blueprint trace clause 1 and proof steps 1--4, trace normalization (blueprint:
def-sfb-diagonal-trace-models). -/
def Model.trace {b : SpTowerShriek.Base l E} {S X : Scheme.{u}} {f : X ⟶ S}
    {cS : Chern l E S} {cP : Chern l E X}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Model l E b S X f cS cP tS tP) [IsIso (p.bq l E)] :
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

/-- Restriction of a varying finite coefficient system to discrete constant scalars.
Its values, arrows, restrictions and transitions retain the underlying groups.
The last equation fixes the action of every l-adic integer by its residue.
Source: blueprint trace proof step 3 (blueprint: def-sfb-diagonal-trace-models). -/
structure Restriction (T : Scheme.{u}) where
  F : Systems T (Arings l E T) ⥤ DiagonalSystems l T
  underlying : ∀ (M : Systems T (Arings l E T)) (n : ℕ) (U : T.ProEtᵒᵖ),
    AddCommGrpCat.of (((F.obj M).obj (op n)).obj.obj U) =
      AddCommGrpCat.of (M.val.obj (op (n, U.unop)))
  restrictions : ∀ (M : Systems T (Arings l E T)) (n : ℕ)
      {U V : T.ProEtᵒᵖ} (f : U ⟶ V),
    HEq ((((F.obj M).obj (op n)).obj.map f).hom.toAddMonoidHom)
      ((M.val.map (Prod.mkHom (𝟙 n) f.unop).op).hom.toAddMonoidHom)
  transitions : ∀ (M : Systems T (Arings l E T)) {m n : ℕ}
      (h : m ≤ n) (U : T.ProEtᵒᵖ),
    HEq ((((F.obj M).map (homOfLE h).op).hom.app U).hom.toAddMonoidHom)
      ((M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom.toAddMonoidHom)
  morphisms : ∀ {M N : Systems T (Arings l E T)} (f : M ⟶ N)
      (n : ℕ) (U : T.ProEtᵒᵖ),
    HEq ((((F.map f).app (op n)).hom.app U).hom.toAddMonoidHom)
      ((f.val.app (op (n, U.unop))).hom.toAddMonoidHom)
  scalars : ∀ (M : Systems T (Arings l E T)) (n : ℕ) (U : T.ProEtᵒᵖ)
      (z : ULift.{u + 1} ℤ_[l]) (x : ((F.obj M).obj (op n)).obj.obj U),
    z • x = ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) • x
  [additive : F.Additive]
  [limits : PreservesFiniteLimits F]
  [colimits : PreservesFiniteColimits F]

attribute [instance] Restriction.additive Restriction.limits Restriction.colimits

end AlgebraicGeometry.ProEtale.DiagonalTrace

namespace AlgebraicGeometry.ProEtale

/-- The universal underived-to-derived arrow on a sheaf in degree zero.
Source: blueprint trace proof step 9 (blueprint: def-sfb-diagonal-trace-models). -/
def diagonalTraceRightSingle
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type a} [Category.{v} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] (R : DiagonalRightDerived F) (N : A) :
    (DerivedCategory.singleFunctor B 0).obj (F.obj N) ⟶
      R.R.obj ((DerivedCategory.singleFunctor A 0).obj N) :=
  (DerivedCategory.singleFunctorIsoCompQ B 0).hom.app (F.obj N) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app N) ≫
    R.η.app ((HomologicalComplex.single A (.up ℤ) 0).obj N) ≫
    R.R.map ((DerivedCategory.singleFunctorIsoCompQ A 0).inv.app N)

/-- The canonical comparison from a cone to its total derived limit.
Source: blueprint trace proof step 5 (blueprint: def-sfb-diagonal-trace-models). -/
def diagonalTraceConeMap
    {A : Type a} [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) (H : ℕᵒᵖ ⥤ A) (c : Cone H) :
    (DerivedCategory.singleFunctor A 0).obj c.pt ⟶
      L.R.obj ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj H) :=
  (DerivedCategory.singleFunctor A 0).map (limit.lift H c) ≫ diagonalOrdinaryRlim L H

/-- Direct image with the completed action is additive on sections.
Source: blueprint trace clause 1 (blueprint: def-sfb-diagonal-trace-models). -/
instance diagonalTracePushAdditive (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) : (diagonalTracePush l f).Additive where
  map_add := rfl

/-- Actual direct image of strict constant-coefficient towers, with quotient transitions.
Source: blueprint trace clause 1 (blueprint: def-sfb-diagonal-trace-models). -/
def diagonalTraceSystemPush (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S) :
    DiagonalSystems l X ⥤ DiagonalSystems l S :=
  (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l X) (DiagonalMod l S)).obj
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)

/-- Additivity of direct image is computed componentwise.
Source: blueprint trace clause 1 (blueprint: def-sfb-diagonal-trace-models). -/
instance diagonalTraceSystemPushAdditive (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) : (diagonalTraceSystemPush l f).Additive where
  map_add := rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- Exact coefficient restriction commutes with derived direct image via the
comparison of its underived functors, with the common-derived-unit equation.
Source: blueprint trace proof steps 3 and 7
(blueprint: def-sfb-diagonal-trace-models). -/
structure ExactSquare
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G) where
  iso : RF.R ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ RG.R
  normalization : ∀ P : CochainComplex A ℤ,
    V.mapDerivedCategory.map (RF.η.app P) ≫ iso.hom.app (DerivedCategory.Q.obj P) ≫
        RG.R.map (U.mapDerivedCategoryFactors.hom.app P) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) ≫
        RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P)

/-- Exact coefficient restriction between independently sized derived categories
commutes with direct image via the underived comparison and full derived-unit equation.
This extends `ExactSquare` without changing its published interface.
Source: blueprint trace proof steps 3 and 7
(blueprint: def-sfb-diagonal-trace-models). -/
structure ExactSquareOfUniverses
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G) where
  iso : RF.R ⋙ V.mapDerivedCategory ≅ U.mapDerivedCategory ⋙ RG.R
  normalization : ∀ P : CochainComplex A ℤ,
    V.mapDerivedCategory.map (RF.η.app P) ≫ iso.hom.app (DerivedCategory.Q.obj P) ≫
        RG.R.map (U.mapDerivedCategoryFactors.hom.app P) =
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) ≫
        RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P)

section LimitSquare

-- The fixed-coefficient zero morphisms differ from those of the abelian structure used by
-- `DerivedCategory.Q`; unifying the two unfolds both abelian structures in the kernel.
attribute [-instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms

/-- The canonical direct-image/limit comparison, fixed by its common derived unit.
The projection equation retains the level maps, rather than only its object values.
Source: blueprint trace proof step 5; Stacks 0A07
(blueprint: def-sfb-diagonal-trace-models). -/
structure LimitSquare (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (LX : DiagonalRlim (DiagonalMod l X)) (LS : DiagonalRlim (DiagonalMod l S))
    (Rf : DiagonalRightDerived
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f))
    (Rt : DiagonalRightDerived (diagonalTraceSystemPush l f)) where
  ordinary : (lim : DiagonalSystems l X ⥤ DiagonalMod l X) ⋙
      lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f ≅
    diagonalTraceSystemPush l f ⋙ lim
  ordinary_eq : ∀ H : DiagonalSystems l X,
    ordinary.hom.app H = limit.post H
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
  iso : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LS.R
  normalization : ∀ P : CochainComplex (DiagonalSystems l X) ℤ,
    Rf.η.app (((lim : DiagonalSystems l X ⥤ DiagonalMod l X).mapHomologicalComplex
      (.up ℤ)).obj P) ≫ Rf.R.map (LX.η.app P) ≫
        iso.hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) ≫
        LS.η.app (((diagonalTraceSystemPush l f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        LS.R.map (Rt.η.app P)

end LimitSquare

end AlgebraicGeometry.ProEtale.DiagonalTrace
namespace AlgebraicGeometry.ProEtale
/-- The comparison for exact scalar functors and an actual cone.
Source: blueprint trace proof step 5 (blueprint: def-sfb-diagonal-trace-models). -/
def exactConeComparison
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C]
    [Abelian A] [Abelian B] [Abelian C] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    [HasDerivedCategory.{wb} (ℕᵒᵖ ⥤ B)] [HasDerivedCategory.{wc} C]
    (U : A ⥤ B) (V : C ⥤ (ℕᵒᵖ ⥤ B))
    [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DiagonalRlim B) (M : A) (N : C)
    (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N) :
    U.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      L.R.obj (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj N)) :=
  (U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
    (DerivedCategory.singleFunctor B 0).map
      (limit.lift (V.obj N) ⟨U.obj M, π⟩) ≫
    diagonalOrdinaryRlim L (V.obj N) ≫
    L.R.map ((V.mapDerivedCategorySingleFunctor 0).inv.app N)
end AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
/-- Shift a specified comparison using the functors' specified shift structures.
Source: blueprint trace clause 1 (blueprint: def-sfb-diagonal-trace-models). -/
def shiftedComparison
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (U : A ⥤ C) (V : B ⥤ C) [U.CommShift ℤ] [V.CommShift ℤ]
    {M : A} {N : B} (h : U.obj M ⟶ V.obj N) (j : ℤ) :
    U.obj (M⟦j⟧) ⟶ V.obj (N⟦j⟧) :=
  (U.commShiftIso j).hom.app M ≫ h⟦j⟧' ≫ (V.commShiftIso j).inv.app N

end AlgebraicGeometry.ProEtale.DiagonalTrace
