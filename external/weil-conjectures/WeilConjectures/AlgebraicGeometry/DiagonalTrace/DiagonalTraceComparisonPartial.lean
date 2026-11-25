/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceChernTwistExistence
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceGeometricModelExistence
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceScalarComparisons

/-! # Partial normalized comparison data for the diagonal trace -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

universe u a v w wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses
section PartialPresentation

-- The fixed-coefficient zero morphisms differ from those of the abelian structure used by
-- `DerivedCategory.Q`; unifying the two unfolds both abelian structures in the kernel.
attribute [-instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms


/-- The comparison data before the two derived-limit invertibility assertions.

Source: `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1), construction of
the geometric, coefficient, and derived comparison fields.
(blueprint: new-sfb-diagonal-trace-comparison-partial).
-/
structure PartialPresentation (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (f : X ⟶ S) [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S] where
  base : SpTowerShriek.Base l E
  chernS : Chern l E S
  chernX : Chern l E X
  normalizedS : chernS.Normalized l E
  normalizedX : chernX.Normalized l E
  finiteS : FiniteChernNormalization l E chernS
  finiteX : FiniteChernNormalization l E chernX
  twistS : Twisting l E chernS
  twistX : Twisting l E chernX
  model : Model l E base S X f chernS chernX twistS twistX
  restrictionS : Restriction l E S
  restrictionX : Restriction l E X
  coefficientsS : Coefficients l E S chernS restrictionS
  coefficientsX : Coefficients l E X chernX restrictionX
  LS : DiagonalRlim (DiagonalMod l S)
  LX : DiagonalRlim (DiagonalMod l X)
  Rf : DiagonalRightDerived
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
  Rt : DiagonalRightDerived (diagonalTraceSystemPush l f)
  Rc : DiagonalRightDerived (diagonalTracePush l f)
  varyingOrdinary : model.geometry.push ⋙ restrictionS.F ≅
    restrictionX.F ⋙ diagonalTraceSystemPush l f
  varying_sections : ∀ (M : Systems X (Arings l E X)) (n : ℕ) (U : S.ProEtᵒᵖ)
      (x : (((model.geometry.push ⋙ restrictionS.F).obj M).obj (op n)).obj.obj U),
    HEq (((varyingOrdinary.hom.app M).app (op n)).hom.app U x) x
  varying : SpTowerShriek.push l E base model.geometry ⋙
      restrictionS.F.mapDerivedCategory ≅ restrictionX.F.mapDerivedCategory ⋙ Rt.R
  varying_normalization : ∀ (P : CochainComplex (Systems X (Arings l E X)) ℤ)
      (hP : P.IsKInjective),
    letI := hP
    letI : model.geometry.push.Additive := model.geometry.pushAdditive
    letI : restrictionS.F.Additive := restrictionS.additive
    letI : restrictionX.F.Additive := restrictionX.additive
    letI : (model.geometry.push ⋙ restrictionS.F).Additive := inferInstance
    letI : (restrictionX.F ⋙ diagonalTraceSystemPush l f).Additive := inferInstance
    varying.hom.app (DerivedCategory.Q.obj P) ≫
        Rt.R.map (restrictionX.F.mapDerivedCategoryFactors.hom.app P) =
      restrictionS.F.mapDerivedCategory.map
          ((model.geometry.push.rightDerivedFunctorObjQIso P).hom) ≫
        restrictionS.F.mapDerivedCategoryFactors.hom.app
          ((model.geometry.push.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex varyingOrdinary.hom (.up ℤ)).app P) ≫
        Rt.η.app ((restrictionX.F.mapHomologicalComplex (.up ℤ)).obj P)
  completedOrdinary : diagonalTracePush l f ⋙ diagonalCompletedRestriction l S ≅
    diagonalCompletedRestriction l X ⋙
      lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  completed_sections : ∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
      (x : ((diagonalTracePush l f ⋙ diagonalCompletedRestriction l S).obj M).obj.obj U),
    HEq ((completedOrdinary.hom.app M).hom.app U x) x
  completed : ExactSquare (diagonalTracePush l f)
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
    (diagonalCompletedRestriction l X) (diagonalCompletedRestriction l S)
    Rc Rf completedOrdinary
  limits : LimitSquare l f LX LS Rf Rt

end PartialPresentation

private theorem normalizedOnKInjective
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    [HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RG : DiagonalRightDerived G) (ordinary : F ⋙ V ≅ U ⋙ G)
    (square : ExactSquareOfUniverses F G U V (canonicalDiagonalRightDerived F)
      RG ordinary) (P : CochainComplex A ℤ) [P.IsKInjective] :
    square.iso.hom.app (DerivedCategory.Q.obj P) ≫
        RG.R.map (U.mapDerivedCategoryFactors.hom.app P) =
      V.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso P).hom ≫
        V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) ≫
        RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := square.normalization P
  change V.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ P) ≫ _ = _ at h
  rw [Functor.rightDerivedFunctorUnitQ_eq] at h
  have h' := congrArg
    (fun k ↦ V.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso P).hom ≫ k) h
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id] at h'
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc] using h'

-- Package the generic fields before specializing to avoid repeated kernel unfolding.
private structure LimitData
    {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive]
    (LX : DiagonalRlim A) (LS : DiagonalRlim B)
    (Rf : DiagonalRightDerived F)
    (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)) where
  ordinary : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
    (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙ lim
  ordinary_eq : ∀ H : ℕᵒᵖ ⥤ A, ordinary.hom.app H = limit.post H F
  iso : LX.R ⋙ Rf.R ≅ Rt.R ⋙ LS.R
  normalization : ∀ P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    Rf.η.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj P) ≫
        Rf.R.map (LX.η.app P) ≫ iso.hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P) ≫
        LS.η.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ LS.R.map (Rt.η.app P)

private theorem limitDataExists
    {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasKInjectiveResolutions A] [HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape ℕᵒᵖ F]
    [((Functor.whiskeringRight ℕᵒᵖ A B).obj F).PreservesKInjectiveComplexes] :
    ∃ (LX : DiagonalRlim A) (LS : DiagonalRlim B) (Rf : DiagonalRightDerived F)
      (Rt : DiagonalRightDerived ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)),
      Nonempty (LimitData F LX LS Rf Rt) := by
  obtain ⟨LX, LS, Rf, Rt, e, c, c₀, h₀, hc, he, hp⟩ :=
    diagonalDirectImage_of_preservesKInjective F
  exact ⟨LX, LS, Rf, Rt, ⟨⟨c₀, h₀, c, hc⟩⟩⟩

private theorem towerKInjective
    {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    (L : B ⥤ A) (F : A ⥤ B) [L.Additive] [F.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ F) :
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).PreservesKInjectiveComplexes := by
  let LT := (Functor.whiskeringRight ℕᵒᵖ B A).obj L
  have : PreservesFiniteLimits LT :=
    ⟨fun _ _ _ ↦ whiskeringRight_preservesLimitsOfShape (C := ℕᵒᵖ) L⟩
  have : PreservesFiniteColimits LT :=
    ⟨fun _ _ _ ↦ whiskeringRight_preservesColimitsOfShape (C := ℕᵒᵖ) L⟩
  have : LT.PreservesHomology := {}
  exact (adj.whiskerRight ℕᵒᵖ).preservesKInjectiveComplexes

private theorem traceLimits (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] (f : X ⟶ S) :
    ∃ (LX : DiagonalRlim (DiagonalMod l X)) (LS : DiagonalRlim (DiagonalMod l S))
      (Rf : DiagonalRightDerived
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f))
      (Rt : DiagonalRightDerived (diagonalTraceSystemPush l f)),
      Nonempty (LimitSquare l f LX LS Rf Rt) := by
  let A := DiagonalMod l X
  let B := DiagonalMod l S
  let : HasDerivedCategory.{u + 1} A :=
    DiagonalTraceLocalizations.mod (ℓ := l) (X := X)
  let : HasDerivedCategory.{u + 1} B :=
    DiagonalTraceLocalizations.mod (ℓ := l) (X := S)
  let : HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ A) :=
    DiagonalTraceLocalizations.systems (ℓ := l) (X := X)
  let : HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ B) :=
    DiagonalTraceLocalizations.systems (ℓ := l) (X := S)
  have : IsGrothendieckAbelian.{u + 1} A :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) X
  have : IsGrothendieckAbelian.{u + 1} B :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) S
  have : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck A
  have : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ B) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck B
  let F := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  have : ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).PreservesKInjectiveComplexes :=
    towerKInjective (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f) F
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
  obtain ⟨LX, LS, Rf, Rt, ⟨data⟩⟩ := limitDataExists.{_, _, u + 1} F
  exact ⟨LX, LS, Rf, Rt, ⟨{
    ordinary := data.ordinary
    ordinary_eq := data.ordinary_eq
    iso := data.iso
    normalization := data.normalization }⟩⟩

/-- The geometric and derived comparison fields can be assembled compatibly.

Proof: construct the Kummer Chern systems, their tensor/Hom twists, the transported
projective-line model, the coefficient restrictions, and the ordinary and derived
direct-image and limit comparisons. The remaining two assertions are exactly the
Milnor invertibility step isolated in `diagonalTraceComparisonLimitIsos`.
(blueprint: new-sfb-diagonal-trace-comparison-partial-existence).
-/
theorem exists_diagonalTraceComparisonPartial
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (m : X ≅ ProjectiveLine S)
    (hm : m.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (l : Γ(S, ⊤))) :
    ∃ p : PartialPresentation l (ULift.{u} (Padic l)) f, p.model.model = m := by
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hS.map f.appTop.hom
  obtain ⟨cS, nS, fS, ⟨tS⟩⟩ := exists_diagonalTraceChernTwist l S hS
  obtain ⟨cX, nX, fX, ⟨tX⟩⟩ := exists_diagonalTraceChernTwist l X hX
  obtain ⟨b, g, hg⟩ := exists_diagonalTraceGeometricModel l f m hm hS cS cX nS nX tS tX
  obtain ⟨LX, LS, Rf, Rt, ⟨limits⟩⟩ := traceLimits l f
  obtain ⟨rS, rX, ⟨aS⟩, ⟨aX⟩, Rc, vo, hvo, ⟨square⟩, co, hco, ⟨completed⟩⟩ :=
    exists_diagonalTraceScalarComparisons l f b g.geometry cS cX nS nX Rf Rt
  let : g.geometry.push.Additive := g.geometry.pushAdditive
  let : rS.F.Additive := rS.additive
  let : rX.F.Additive := rX.additive
  let : PreservesFiniteLimits rS.F := rS.limits
  let : PreservesFiniteColimits rS.F := rS.colimits
  let : PreservesFiniteLimits rX.F := rX.limits
  let : PreservesFiniteColimits rX.F := rX.colimits
  let : HasKInjectiveResolutions (Systems X (Arings l (ULift.{u} (Padic l)) X)) :=
    b.kinjective X
  refine ⟨{
    base := b
    chernS := cS
    chernX := cX
    normalizedS := nS
    normalizedX := nX
    finiteS := fS
    finiteX := fX
    twistS := tS
    twistX := tX
    model := g
    restrictionS := rS
    restrictionX := rX
    coefficientsS := aS
    coefficientsX := aX
    LS := LS
    LX := LX
    Rf := Rf
    Rt := Rt
    Rc := Rc
    varyingOrdinary := vo
    varying_sections := hvo
    varying := square.iso
    varying_normalization := ?_
    completedOrdinary := co
    completed_sections := hco
    completed := completed
    limits := limits }, hg⟩
  intro P hP
  let := hP
  exact normalizedOnKInjective g.geometry.push (diagonalTraceSystemPush l f)
    rX.F rS.F Rt vo square P

end AlgebraicGeometry.ProEtale.DiagonalTrace
