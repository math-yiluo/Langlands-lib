/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalization
public import WeilConjectures.AlgebraicGeometry.ScalarPullbackSquareCoherence
import all WeilConjectures.AlgebraicGeometry.ScalarPullbackSquareCoherence
import all WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.AlgebraicGeometry.SectionPullNormalizationTransport

/-! # Scalar extension and geometric exchange

proof.md, (2),
coefficient devissage; Stacks Project, sites-cohomology.tex, Tags 07A7 and 0E47
(auxiliary; not a blueprint node).

All functors are the existing ordinary unbounded internal-module derived functors.
The balancing maps are specified by their universal computation-counit normalization.
The direct-image maps are their actual mates, without an invertibility assumption.
-/

@[expose] public noncomputable section

set_option linter.all false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

attribute [local irreducible] CategoryTheory.mateEquiv
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedFunctor
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullback
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushforward
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedAdjunction
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullbackComposition
  AlgebraicGeometry.ProEtale.QuotientChange.scalarSectionPullComparison

namespace CategoryTheory

/-- The left route in a square of mates, with endpoint types kept abstract.
Source: Stacks 0E47 (auxiliary; not a blueprint node). -/
def mateRouteLeft
    {A₀ A₁ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₃]
    [Category* B₀] [Category* B₁] [Category* B₂] [Category* B₃]
    {rf : A₁ ⥤ A₀} {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁}
    {rfb : B₁ ⥤ B₀} {ab : B₁ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    {a : A₁ ⥤ A₃} {T₃ : A₃ ⥤ B₃}
    (cb : B₀ ⥤ B₂) (r : rf ⋙ T₀ ⟶ T₁ ⋙ rfb)
    (eb : rfb ⋙ cb ⟶ ab ⋙ rgb) (la : T₁ ⋙ ab ⟶ a ⋙ T₃) (J : A₁) :
    cb.obj (T₀.obj (rf.obj J)) ⟶ rgb.obj (T₃.obj (a.obj J)) :=
  cb.map (r.app J) ≫ eb.app (T₁.obj J) ≫ rgb.map (la.app J)

/-- The right route in a square of mates, with endpoint types kept abstract.
Source: Stacks 0E47 (auxiliary; not a blueprint node). -/
def mateRouteRight
    {A₀ A₁ A₂ A₃ B₀ B₂ B₃ : Type*}
    [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]
    [Category* B₀] [Category* B₂] [Category* B₃]
    {rf : A₁ ⥤ A₀} {c : A₀ ⥤ A₂} {rg : A₃ ⥤ A₂}
    {a : A₁ ⥤ A₃} {T₀ : A₀ ⥤ B₀} {T₃ : A₃ ⥤ B₃}
    {cb : B₀ ⥤ B₂} {rgb : B₃ ⥤ B₂}
    (T₂ : A₂ ⥤ B₂) (lc : T₀ ⋙ cb ⟶ c ⋙ T₂)
    (e : rf ⋙ c ⟶ a ⋙ rg) (t : rg ⋙ T₂ ⟶ T₃ ⋙ rgb) (J : A₁) :
    cb.obj (T₀.obj (rf.obj J)) ⟶ rgb.obj (T₃.obj (a.obj J)) :=
  lc.app (rf.obj J) ≫ T₂.map (e.app J) ≫ t.app (a.obj J)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

/-- The existing ambient exchange with the named internal functor interfaces exposed.
This changes only its type presentation, retaining the exact unit-square-counit map.
Source: Stacks 07A7 (auxiliary; not a blueprint node). -/
def scalarAmbientExchange (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    F R f ⋙ L R c ⟶ L R a ⋙ F R f' :=
  (mateEquiv (adj R f) (adj R f')
    (TwoSquare.mk _ _ _ _ (scalarPullbackSquare R sq).hom)).natTrans

/-- The first route of the normalized rectangle: scalar/direct-image mate, exchange
at the new coefficients, then the top-edge balancing map under direct image.
Source: Stacks 07A7 and 0E47; blueprint coefficient devissage, (2)
(auxiliary; not a blueprint node). -/
def scalarExchangeLeft (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (J : DerivedCategory (Modules Λ X)) :
    (L Λ' c).obj ((D φ Y).obj ((F Λ f).obj J)) ⟶
      (F Λ' f').obj ((D φ X').obj ((L Λ a).obj J)) :=
  mateRouteLeft (L Λ' c) (rho φ f (b f)) (scalarAmbientExchange Λ' sq)
    (b a).hom J

/-- The second route: balancing along the bottom edge, scalar extension of exchange,
then the left-edge scalar/direct-image mate.
Source: Stacks 07A7 and 0E47; blueprint coefficient devissage, (2)
(auxiliary; not a blueprint node). -/
def scalarExchangeRight (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (J : DerivedCategory (Modules Λ X)) :
    (L Λ' c).obj ((D φ Y).obj ((F Λ f).obj J)) ⟶
      (F Λ' f').obj ((D φ X').obj ((L Λ a).obj J)) :=
  mateRouteRight (D φ C) (b c).hom (scalarAmbientExchange Λ sq)
    (rho φ f' (b f')) J

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

/-- The geometric realization's forward map is the mate of its inverse pullback map.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
theorem scalarSectionPushMate_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {U V : Scheme.{u}} (h : U ⟶ V) :
    (mateEquiv (adj R h) (ModuleRingedComparison.derivedAdjunction R h)
      (TwoSquare.mk _ _ _ _ (scalarSectionPullComparison R h).inv)).natTrans =
        (by
          unfold F CondensedRing.moduleObjectDerivedPushforward
          exact (ModuleRingedComparison.derivedPushComparison R h).hom) := by
  have ht := ModuleRingedComparison.derivedMate R h
  unfold ModuleRingedComparison.normalizationInternalAdjunction
    ModuleRingedComparison.internalDerivedPullback
    ModuleRingedComparison.internalDerivedPushforward
    ModuleRingedComparison.comparisonSource at ht
  unfold adj scalarSectionPullComparison L F
    CondensedRing.moduleObjectDerivedPullback CondensedRing.moduleObjectDerivedPushforward
  exact ht

/-- The fixed pushforward realization with the named internal interface exposed.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def scalarSectionPushComparison
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {U V : Scheme.{u}} (h : U ⟶ V) :
    F R h ⋙ ModuleRingedComparison.derivedFunctor R V ≅
      ModuleRingedComparison.derivedFunctor R U ⋙
        ModuleRingedComparison.derivedPushforward R h :=
  by
    let e : F R h ⋙ ModuleRingedComparison.derivedFunctor R V ≅
        ModuleRingedComparison.derivedFunctor R U ⋙
          ModuleRingedComparison.derivedPushforward R h := by
      unfold F CondensedRing.moduleObjectDerivedPushforward
      exact ModuleRingedComparison.derivedPushComparison R h
    have hm : (mateEquiv (adj R h) (ModuleRingedComparison.derivedAdjunction R h)
        (TwoSquare.mk _ _ _ _ (scalarSectionPullComparison R h).inv)).natTrans = e.hom := by
      exact scalarSectionPushMate_eq R h
    exact
      { hom := (mateEquiv (adj R h) (ModuleRingedComparison.derivedAdjunction R h)
          (TwoSquare.mk _ _ _ _ (scalarSectionPullComparison R h).inv)).natTrans
        inv := e.inv
        hom_inv_id := (congrArg (fun t ↦ t ≫ e.inv) hm).trans e.hom_inv_id
        inv_hom_id := (congrArg (fun t ↦ e.inv ≫ t) hm).trans e.inv_hom_id }

/-- The section realization equation fixes the balancing isomorphism supplied by
normalized pullback data. All other factors are invertible and realization is an
equivalence, so the displayed property determines this isomorphism uniquely.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
theorem sectionRectangleLambda_witness (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (p : SectionPullNormalized φ h sU sV b) :
    ∃ d : sV.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' h ≅
        ModuleRingedComparison.derivedPullback Λ h ⋙ sU.pair.derived,
      ∀ M : DerivedCategory (Modules Λ V),
        (ModuleRingedComparison.derivedEquivalence Λ' U).functor.map (b.hom.app M) ≫
            sU.derived.hom.app ((L Λ h).obj M) ≫
            sU.pair.derived.map ((scalarSectionPullComparison Λ h).hom.app M) =
          (scalarSectionPullComparison Λ' h).hom.app ((D φ V).obj M) ≫
            (ModuleRingedComparison.derivedPullback Λ' h).map (sV.derived.hom.app M) ≫
            d.hom.app ((ModuleRingedComparison.derivedEquivalence Λ V).functor.obj M) := by
  exact ⟨p.choose_spec.2.choose_spec.2.choose,
    p.choose_spec.2.choose_spec.2.choose_spec.2⟩

/-- The section K-flat balancing isomorphism supplied by SectionPullNormalized.
Its representative square uses the ordinary conjugate of the identity on sections.
The final comparison equation uniquely determines this d: the section realization
is essentially surjective and every other factor is invertible. Thus this choice
selects the specified comparison, rather than an undetermined scalar isomorphism.
Source: Stacks 03EK, 07A6, 0D6D
(auxiliary; not a blueprint node). -/
def sectionRectangleLambda (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (p : SectionPullNormalized φ h sU sV b) :
    sV.pair.derived ⋙ ModuleRingedComparison.derivedPullback Λ' h ≅
      ModuleRingedComparison.derivedPullback Λ h ⋙ sU.pair.derived :=
  (sectionRectangleLambda_witness φ h sU sV b p).choose

/-- Section rho is the actual mate of the normalized section lambda under the
independently specified ringed derived geometric adjunctions.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def sectionRectangleRho (φ : Λ ⟶ Λ') [IsMonHom φ]
    {U V : Scheme.{u}} (h : U ⟶ V)
    (sU : SectionScalarComparison φ U) (sV : SectionScalarComparison φ V)
    (b : D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (p : SectionPullNormalized φ h sU sV b) :
    ModuleRingedComparison.derivedPushforward Λ h ⋙ sV.pair.derived ⟶
      sU.pair.derived ⋙ ModuleRingedComparison.derivedPushforward Λ' h :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction Λ h)
    (ModuleRingedComparison.derivedAdjunction Λ' h)
    (TwoSquare.mk _ _ _ _ (sectionRectangleLambda φ h sU sV b p).hom)).natTrans

/-- Section exchange is the mate of the section geometric square compositor.
This is the word in the last conjunct of GeometricAgreement, with g'=a and g=c.
Source: Stacks 07A7, 0E47 (auxiliary; not a blueprint node). -/
def sectionRectangleExchange
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c) :
    ModuleRingedComparison.derivedPushforward R f ⋙
        ModuleRingedComparison.derivedPullback R c ⟶
      ModuleRingedComparison.derivedPullback R a ⋙
        ModuleRingedComparison.derivedPushforward R f' :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction R f)
    (ModuleRingedComparison.derivedAdjunction R f')
    (TwoSquare.mk _ _ _ _
      ((ModuleRingedComparison.derivedPullbackComposition R f' c).symm ≪≫
        eqToIso (congrArg
          (fun k : X' ⟶ Y ↦ ModuleRingedComparison.derivedPullback R k)
          sq.toCommSq.w.symm) ≪≫
        ModuleRingedComparison.derivedPullbackComposition R a f).hom)).natTrans

/-- Source comparison: geometric pullback, scalar comparison, then geometric pushforward.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def sectionRectangleSource (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X C Y : Scheme.{u}} (f : X ⟶ Y) (c : C ⟶ Y)
    (sY : SectionScalarComparison φ Y) (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedFunctor Λ' C).obj
        ((L Λ' c).obj ((D φ Y).obj ((F Λ f).obj J))) ≅
      (ModuleRingedComparison.derivedPullback Λ' c).obj
        (sY.pair.derived.obj ((ModuleRingedComparison.derivedPushforward Λ f).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) :=
  (scalarSectionPullComparison Λ' c).app ((D φ Y).obj ((F Λ f).obj J)) ≪≫
    (ModuleRingedComparison.derivedPullback Λ' c).mapIso
      (sY.derived.app ((F Λ f).obj J) ≪≫
        sY.pair.derived.mapIso ((scalarSectionPushComparison Λ f).app J))

/-- Target comparison: geometric pushforward, scalar comparison, then geometric pullback.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def sectionRectangleTarget (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C : Scheme.{u}} (a : X' ⟶ X) (f' : X' ⟶ C)
    (sX' : SectionScalarComparison φ X') (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedFunctor Λ' C).obj
        ((F Λ' f').obj ((D φ X').obj ((L Λ a).obj J))) ≅
      (ModuleRingedComparison.derivedPushforward Λ' f').obj
        (sX'.pair.derived.obj ((ModuleRingedComparison.derivedPullback Λ a).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) :=
  (scalarSectionPushComparison Λ' f').app ((D φ X').obj ((L Λ a).obj J)) ≪≫
    (ModuleRingedComparison.derivedPushforward Λ' f').mapIso
      (sX'.derived.app ((L Λ a).obj J) ≪≫
        sX'.pair.derived.mapIso ((scalarSectionPullComparison Λ a).app J))

/-- The normalized section rectangle's first route, using the actual section rho,
section exchange at the new coefficients and section lambda along a.
Source: Stacks 07A7, 0E47 (auxiliary; not a blueprint node). -/
def sectionRectangleLeft (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V), D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (s : ∀ T : Scheme.{u}, SectionScalarComparison φ T)
    (p : ∀ {U V : Scheme.{u}} (h : U ⟶ V), SectionPullNormalized φ h (s U) (s V) (b h))
    (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedPullback Λ' c).obj
        ((s Y).pair.derived.obj ((ModuleRingedComparison.derivedPushforward Λ f).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) ⟶
      (ModuleRingedComparison.derivedPushforward Λ' f').obj
        ((s X').pair.derived.obj ((ModuleRingedComparison.derivedPullback Λ a).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) :=
  mateRouteLeft (ModuleRingedComparison.derivedPullback Λ' c)
    (sectionRectangleRho φ f (s X) (s Y) (b f) (p f))
    (sectionRectangleExchange Λ' sq)
    (sectionRectangleLambda φ a (s X') (s X) (b a) (p a)).hom
    ((ModuleRingedComparison.derivedFunctor Λ X).obj J)

/-- The normalized section rectangle's second route: lambda along c, old-coefficient
section exchange under scalar extension, and section rho along f'.
Source: Stacks 07A7, 0E47 (auxiliary; not a blueprint node). -/
def sectionRectangleRight (φ : Λ ⟶ Λ') [IsMonHom φ]
    {X' X C Y : Scheme.{u}} {a : X' ⟶ X} {c : C ⟶ Y}
    {f : X ⟶ Y} {f' : X' ⟶ C} (sq : ChosenCartesianSquare a f' f c)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V), D φ V ⋙ L Λ' h ≅ L Λ h ⋙ D φ U)
    (s : ∀ T : Scheme.{u}, SectionScalarComparison φ T)
    (p : ∀ {U V : Scheme.{u}} (h : U ⟶ V), SectionPullNormalized φ h (s U) (s V) (b h))
    (J : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedPullback Λ' c).obj
        ((s Y).pair.derived.obj ((ModuleRingedComparison.derivedPushforward Λ f).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) ⟶
      (ModuleRingedComparison.derivedPushforward Λ' f').obj
        ((s X').pair.derived.obj ((ModuleRingedComparison.derivedPullback Λ a).obj
          ((ModuleRingedComparison.derivedFunctor Λ X).obj J))) :=
  mateRouteRight (s C).pair.derived
    (sectionRectangleLambda φ c (s C) (s Y) (b c) (p c)).hom
    (sectionRectangleExchange Λ sq)
    (sectionRectangleRho φ f' (s X') (s C) (b f') (p f'))
    ((ModuleRingedComparison.derivedFunctor Λ X).obj J)

attribute [local irreducible] scalarAmbientExchange scalarExchangeLeft scalarExchangeRight
  scalarSectionPushComparison sectionRectangleLambda sectionRectangleRho
  sectionRectangleExchange sectionRectangleSource sectionRectangleTarget
  sectionRectangleLeft sectionRectangleRight

attribute [local irreducible] rho SectionPullNormalized SectionScalarNormalized

end AlgebraicGeometry.ProEtale.QuotientChange
