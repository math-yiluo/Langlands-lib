/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import all WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import all WeilConjectures.AlgebraicGeometry.QuotientChange.NormalizedScalarRestrictionPush
import WeilConjectures.AlgebraicGeometry.QuotientChange.NormalizedScalarSectionFamily

/-! # Reduction of the actual unbounded integral exchange

The equality is an equality of natural transformations. Its section-module realization
uses the independently specified ringed adjunctions and geometric compositors. Scalar
comparisons retain their balanced-generator and K-flat computation normalizations.
As in the direct-image comparison, n denotes quotient exponent n + 1.

## References

* Stacks Project, Tags 07A7, 0E47 and 0E48
* Stacks 0D6D and 07A7
* Stacks 07A6
* Stacks 03EK, 06YY and 09T5
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale.QuotientChange
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  mateEquiv AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedFunctor
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullback
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushforward
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedAdjunction
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPushComparison
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.derivedPullbackComposition
  AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarComp

open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct ChangeOfRings

private theorem route_natTrans_ext
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category B₀] [Category B₁] [Category B₂] [Category B₃]
    {rf : A₁ ⥤ A₀} {c : A₀ ⥤ A₂} {rg : A₃ ⥤ A₂} {h : A₁ ⥤ A₃}
    {T₀ : A₀ ⥤ B₀} {T₁ : A₁ ⥤ B₁} {T₃ : A₃ ⥤ B₃}
    {rfb : B₁ ⥤ B₀} {ab : B₁ ⥤ B₃} {rgb : B₃ ⥤ B₂}
    (cb : B₀ ⥤ B₂) (T₂ : A₂ ⥤ B₂)
    (r : rf ⋙ T₀ ⟶ T₁ ⋙ rfb) (eb : rfb ⋙ cb ⟶ ab ⋙ rgb)
    (la : T₁ ⋙ ab ⟶ h ⋙ T₃) (lc : T₀ ⋙ cb ⟶ c ⋙ T₂)
    (e : rf ⋙ c ⟶ h ⋙ rg) (t : rg ⋙ T₂ ⟶ T₃ ⋙ rgb)
    (he : ∀ J, mateRouteLeft cb r eb la J = mateRouteRight T₂ lc e t J) :
    Functor.whiskerRight r cb ≫ Functor.whiskerLeft T₁ eb ≫
        Functor.whiskerRight la rgb =
      Functor.whiskerLeft rf lc ≫ Functor.whiskerRight e T₂ ≫
        Functor.whiskerLeft h t := by
  apply NatTrans.ext
  funext J
  exact he J

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The recorded actual ambient exchange, with the direct-image comparison's typed
interfaces. -/
def ambient (sq : ChosenCartesianSquare h f' f g) :
    F Λ f ⋙ L Λ g ⟶ L Λ h ⋙ F Λ f' :=
  (mateEquiv (adj Λ f) (adj Λ f')
    (TwoSquare.mk _ _ _ _ (scalarPullbackSquare Λ sq).hom))

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]

/-- The independently specified section-module geometric square: compose the actual
ringed derived pullbacks along the two equal scheme composites. -/
def sectionSquare (sq : ChosenCartesianSquare h f' f g) :
    ModuleRingedComparison.derivedPullback Λ g ⋙
        ModuleRingedComparison.derivedPullback Λ f' ≅
      ModuleRingedComparison.derivedPullback Λ f ⋙
        ModuleRingedComparison.derivedPullback Λ h :=
  (ModuleRingedComparison.derivedPullbackComposition Λ f' g).symm ≪≫
    eqToIso (congrArg
      (fun k : X' ⟶ Y ↦ ModuleRingedComparison.derivedPullback Λ k)
      sq.toCommSq.w.symm) ≪≫
    ModuleRingedComparison.derivedPullbackComposition Λ h f

/-- The actual ringed exchange, formed with the independently derived section-module
adjunctions and the geometric square, before any completeness condition. -/
def sectionExchange (sq : ChosenCartesianSquare h f' f g) :
    ModuleRingedComparison.derivedPushforward Λ f ⋙
        ModuleRingedComparison.derivedPullback Λ g ⟶
      ModuleRingedComparison.derivedPullback Λ h ⋙
        ModuleRingedComparison.derivedPushforward Λ f' :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction Λ f)
    (ModuleRingedComparison.derivedAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (sectionSquare Λ sq).hom))

/-- The existing normalized pullback comparison, with its internal endpoint made explicit. -/
def pullSection {U V : Scheme.{u}} (u : U ⟶ V) :
    L Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ U ≅
      ModuleRingedComparison.derivedFunctor Λ V ⋙ ModuleRingedComparison.derivedPullback Λ u :=
  scalarSectionPullComparison Λ u

/-- The existing normalized pushforward comparison, with its internal endpoint explicit. -/
def pushSection {U V : Scheme.{u}} (u : U ⟶ V) :
    F Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ V ≅
      ModuleRingedComparison.derivedFunctor Λ U ⋙
        ModuleRingedComparison.derivedPushforward Λ u :=
  scalarSectionPushComparison Λ u

attribute [local irreducible] ambient sectionSquare sectionExchange pullSection pushSection
  scalarAmbientExchange scalarSectionPushComparison scalarSectionPullComparison
  sectionRectangleExchange

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)] in
private theorem ambient_eq_scalar (sq : ChosenCartesianSquare h f' f g) :
    ambient Λ sq = scalarAmbientExchange Λ sq := by
  delta ambient scalarAmbientExchange
  rfl

end Ambient

set_option allowUnsafeReducibility true
attribute [local semireducible] ModuleRingedComparison.derivedFunctor

/-- Ordinary balanced generators and K-flat computation characterize the scalar
realization, before specializing the coefficient map. -/
def ScalarComparisonRealized
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]
    (a : R ⟶ S) [IsMonHom a] (T : Scheme.{u})
    (q : SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring R T)
      (S := ModuleRingedComparison.ring S T)
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (coefficientMap a T)))
    (e₀ : extension a T ⋙
        (ModuleRingedComparison.equivalence S T).functor ≅
      (ModuleRingedComparison.equivalence R T).functor ⋙ q.extension)
    (e : D a T ⋙
        ModuleRingedComparison.derivedFunctor S T ≅
      ModuleRingedComparison.derivedFunctor R T ⋙ q.derived) : Prop :=
  (∀ (M : Modules R T) (U : T.ProEtᵒᵖ)
      (s : (condensedRingObj S T).obj.obj U) (m : M.X.obj.obj U),
    ((eqToHom (q.extension_obj
      ((ModuleRingedComparison.equivalence R T).functor.obj M))).val.app U)
        ((e₀.hom.app M).val.app U
          (InternalAbelianSheafModule.internalScalarGenerator (Scheme.ProEt.topology T)
            (coefficientMap a T) M U s m)) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf
          (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (coefficientMap a T))
          ((ModuleRingedComparison.equivalence R T).functor.obj M)).presheaf).app U
        (s ⊗ₜ[(ModuleRingedComparison.ring R T).obj.obj U,
            ((InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology T) (coefficientMap a T)).hom.app U).hom] m)) ∧
  (∀ P : CochainComplex (Modules R T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients
        (R := ModuleRingedComparison.ring R T)
        (((ModuleRingedComparison.equivalence R T).functor.mapHomologicalComplex
          (.up ℤ)).obj P) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring R T)
      ((ModuleRingedComparison.equivalence R T).functor.obj (P.X i))) →
    (ModuleRingedComparison.derivedFunctor S T).map
        (compute a T P) ≫
        (Functor.mapDerivedCategoryFactors
          (ModuleRingedComparison.equivalence S T).functor).hom.app
            (((extension a T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e₀ (.up ℤ)).hom.app P) =
      e.hom.app (DerivedCategory.Q.obj P) ≫
        q.derived.map
          (ModuleRingedComparison.sectionLocalizationComparison R T P).hom ≫
        SheafOfModules.scalarPairComplexComparison q.extension q.extension_additive
          q.derived q.counit
          (((ModuleRingedComparison.equivalence R T).functor.mapHomologicalComplex
          (.up ℤ)).obj P))

section ScalarSectionRealization

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]
  (a : R ⟶ S) [IsMonHom a]

private theorem internal_rectangle
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      D a V ⋙ L S u ≅ L R u ⋙ D a U)
    (hb : ∀ {U V : Scheme.{u}} (u : U ⟶ V), PullNormalized a u (b u))
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare h f' f g) :
    (Functor.whiskerRight (rho a f (b f)) (L S g) ≫
        Functor.whiskerLeft (D a X) (ambient S sq) ≫
        Functor.whiskerRight (b h).hom (F S f') =
      Functor.whiskerLeft (F R f) (b g).hom ≫
        Functor.whiskerRight (ambient R sq) (D a Y') ≫
        Functor.whiskerLeft (L R h) (rho a f' (b f'))) := by
  simp only [ambient_eq_scalar]
  exact route_natTrans_ext (L S g) (D a Y')
    (rho a f (b f)) (scalarAmbientExchange S sq) (b h).hom (b g).hom
    (scalarAmbientExchange R sq) (rho a f' (b f'))
    (fun K ↦ (scalar_geometric_exchange_rectangle a sq b hb K).1)

/-- The actual section scalar/geometric mate for a general coefficient map. -/
def sectionScalarProjection
    (q : ∀ T : Scheme.{u}, SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring R T)
      (S := ModuleRingedComparison.ring S T)
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (coefficientMap a T)))
    {U V : Scheme.{u}} (u : U ⟶ V)
    (χ : (q V).derived ⋙ ModuleRingedComparison.derivedPullback S u ≅
      ModuleRingedComparison.derivedPullback R u ⋙ (q U).derived) :
    ModuleRingedComparison.derivedPushforward R u ⋙ (q V).derived ⟶
      (q U).derived ⋙ ModuleRingedComparison.derivedPushforward S u :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction R u)
    (ModuleRingedComparison.derivedAdjunction S u)
    (TwoSquare.mk _ _ _ _ χ.hom))

attribute [local irreducible] ScalarComparisonRealized sectionScalarProjection
  SectionScalarNormalized SectionPullNormalized rho scalarExchangeLeft scalarExchangeRight
  sectionRectangleLambda sectionRectangleRho sectionRectangleLeft sectionRectangleRight
  sectionRectangleSource sectionRectangleTarget

end ScalarSectionRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual finite projection reconstructed as a section-ring map. -/
abbrev sectionReduction (T : Scheme.{u}) (n : ℕ) :
    ModuleRingedComparison.ring (integral l E) T ⟶
      ModuleRingedComparison.ring (finite l E n) T :=
  InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (coefficientMap (reduction l E n) T)

variable (n : ℕ)
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (integral l E) T)]
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (finite l E n) T)]

/-- The specified finite projection in section coordinates: it is the counit-adjunct
mate of the normalized scalar/pullback comparison under the actual ringed adjunctions. -/
def sectionProjection
    (q : ∀ T : Scheme.{u}, SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      (S := ModuleRingedComparison.ring (finite l E n) T) (sectionReduction l E T n))
    {U V : Scheme.{u}} (u : U ⟶ V)
    (χ : (q V).derived ⋙ ModuleRingedComparison.derivedPullback (finite l E n) u ≅
      ModuleRingedComparison.derivedPullback (integral l E) u ⋙ (q U).derived) :
    ModuleRingedComparison.derivedPushforward (integral l E) u ⋙ (q V).derived ⟶
      (q U).derived ⋙ ModuleRingedComparison.derivedPushforward (finite l E n) u :=
  sectionScalarProjection (reduction l E n) q u χ

variable
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      D (reduction l E n) V ⋙ L (finite l E n) u ≅
        L (integral l E) u ⋙ D (reduction l E n) U)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}

end AlgebraicGeometry.ProEtale.IntegralQuotient
