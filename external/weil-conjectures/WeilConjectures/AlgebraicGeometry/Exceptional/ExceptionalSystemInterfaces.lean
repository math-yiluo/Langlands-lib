/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Exceptional adjunction on strict pro-etale coefficient systems

Source: Zheng, Construction 4.1, Lemmas 4.10 and 5.22, Proposition 5.24;
blueprint exceptional inverse-image construction, system transport steps 8--9
(blueprint: lem-sf-exceptional-system-transport).

All comparisons are maps of derived strict systems before evaluation. The integer
index `n` denotes the positive coefficient exponent `n+1`. The records package
conclusions of the existence theorem, rather than additional geometric hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] CategoryTheory.mateEquiv CategoryTheory.conjugateEquiv
attribute [local irreducible] DerivedCategory.Q
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
private instance (priority := 20000) cachedProSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance 20000] strictEtaleRingCompose strictEtaleRingSetCompose
  strictEtaleAddCommGrpSetCompose strictEtaleAddCommGrpSheafify
  strictEtaleCommRingSheafify strictEtaleTypeSheafify strictEtaleAddCommGrpLocal

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: lem-sf-exceptional-system-transport). -/
instance (priority := 5000) exceptionalTransportProEtaleCommRingSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} := inferInstance

attribute [local instance 5000] WeilConjectures.sfAbSheafify

attribute [local instance 5000] WeilConjectures.sfAbBijective

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: lem-sf-exceptional-system-transport). -/
instance (priority := 5000) exceptionalTransportProEtaleRingCompose (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: lem-sf-exceptional-system-transport). -/
instance (priority := 5000) exceptionalTransportProEtaleTypeSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) (Type (u + 1)) := inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: lem-sf-exceptional-system-transport). -/
instance (priority := 5000) exceptionalTransportProEtaleRingSetCompose (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1}) :=
      inferInstance

/-- Cache the existing small-site coefficient witness; no site is changed.
Source: Stacks 00W1 (blueprint: lem-sf-exceptional-system-transport). -/
instance (priority := 5000) exceptionalTransportProEtaleAddCommGrpSetCompose (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      inferInstance

attribute [local instance 20000] exceptionalTransportProEtaleCommRingSheafify
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
  exceptionalTransportProEtaleTypeSheafify exceptionalTransportProEtaleRingCompose
  exceptionalTransportProEtaleRingSetCompose exceptionalTransportProEtaleAddCommGrpSetCompose

/-- Use Mathlib's standard localization for the strict system category.
Source: Zheng, Construction 4.1; Stacks Tag 05RU
(blueprint: lem-sf-exceptional-system-transport). -/
@[irreducible]
instance (priority := 100) exceptionalProSystemDerived (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) :
    HasDerivedCategory.{u + 2} (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) :=
  HasDerivedCategory.standard _
/-- Use the same standard localization at every finite coefficient level.
Source: Zheng, Construction 4.1; Stacks Tag 05RU
(blueprint: lem-sf-exceptional-system-transport). -/
@[irreducible]
instance (priority := 100) exceptionalProLevelDerived (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) (n : ℕ) :
    HasDerivedCategory.{u + 2} (coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n) :=
  HasDerivedCategory.standard _

/-- Cache the already existing additive evaluation instance at the concrete site size.
Source: Zheng Construction 4.1 (blueprint: lem-sf-exceptional-system-transport). -/
instance (priority := 3000) exceptionalProEvaluationAdditive
    (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (ell : O) :
    ∀ n, (coefficientEvaluation.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).Additive :=
  fun n ↦ coefficientEvaluation_additive.{u + 1, u, u + 1} n

/-- The canonical pro-etale set-sheaf image, with its full strict-system normalization.
Source: Zheng Construction 4.1 and Lemma 4.10
(blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalProOrdinaryImage (O : Type (u + 1)) [CommRing O] (ell : O)
    {T S : Scheme.{u}} (g : T ⟶ S) :=
  CoefficientSystemOrdinaryImage (J := Scheme.ProEt.topology S)
    (K := Scheme.ProEt.topology T) O ell _ _
    (Scheme.proEtaleSheafAdjunction g (Type (u + 1)))

/-- Derived evaluation on the actual strict pro-etale systems.
Source: Zheng Construction 4.1 (blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalProEvaluation (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (ell : O) :=
  CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
    (J := Scheme.ProEt.topology T) (O := O) (ell := ell)

variable (O : Type (u + 1)) [CommRing O] (ell : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

variable (PX : ExceptionalProEvaluation X O ell) (PY : ExceptionalProEvaluation Y O ell)
  (PZ : ExceptionalProEvaluation c.Z O ell)

/-- Termwise pro-etale open extension and the universal proper derived image.
The open functor is the left adjoint of geometric restriction; all evaluations
and localizations are included to fix the maps before evaluation.
Source: Zheng Constructions 4.1 and 5.15
(blueprint: lem-sf-exceptional-system-transport). -/
structure ExceptionalProCompactSupportData where
  openImage : ExceptionalProOrdinaryImage O ell c.i
  properImage : ExceptionalProOrdinaryImage O ell c.g
  properDerived : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
    (J := Scheme.ProEt.topology Y)
    (K := Scheme.ProEt.topology c.Z) O ell _ _ _ properImage PY PZ
  openExtension : CoefficientSystem (J := Scheme.ProEt.topology X) O ell ⥤
    CoefficientSystem (J := Scheme.ProEt.topology c.Z) O ell
  [openAdditive : openExtension.Additive]
  openAdjunction : openExtension ⊣ openImage.inverse
  levelOpen : ∀ n, coefficientLevelModules (J := Scheme.ProEt.topology X) O ell n ⥤
    coefficientLevelModules (J := Scheme.ProEt.topology c.Z) O ell n
  [levelOpenAdditive : ∀ n, (levelOpen n).Additive]
  levelOpenAdjunction : ∀ n, levelOpen n ⊣ (openImage.lift n).modules
  openEvaluation : ∀ n, openExtension ⋙ coefficientEvaluation
    (J := Scheme.ProEt.topology c.Z) (O := O) (ell := ell) n ≅
    coefficientEvaluation (J := Scheme.ProEt.topology X) (O := O) (ell := ell) n ⋙ levelOpen n
  derivedOpen : DerivedCategory (CoefficientSystem (J := Scheme.ProEt.topology X) O ell) ⥤
    DerivedCategory (CoefficientSystem (J := Scheme.ProEt.topology c.Z) O ell)
  openDerived : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
    (J := Scheme.ProEt.topology c.Z)
    (K := Scheme.ProEt.topology X) O ell _ _ _ openImage PZ PX
  derivedOpenAdjunction : derivedOpen ⊣ openDerived.system.inverse
  openFactors : DerivedCategory.Q ⋙ derivedOpen ≅
    openExtension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  levelDerivedOpen : ∀ n,
    DerivedCategory (coefficientLevelModules (J := Scheme.ProEt.topology X) O ell n) ⥤
    DerivedCategory (coefficientLevelModules (J := Scheme.ProEt.topology c.Z) O ell n)
  levelDerivedOpenAdjunction : ∀ n, levelDerivedOpen n ⊣ (openDerived.level n).inverse
  levelOpenFactors : ∀ n, DerivedCategory.Q ⋙ levelDerivedOpen n ≅
    (levelOpen n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  openDerivedEvaluation : ∀ n, derivedOpen ⋙ PZ.evaluation n ≅
    PX.evaluation n ⋙ levelDerivedOpen n

attribute [instance] ExceptionalProCompactSupportData.openAdditive
  ExceptionalProCompactSupportData.levelOpenAdditive

/-- The specified data and canonical coherence of `ExceptionalProCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalProCompactSupportCoherence
    (record : ExceptionalProCompactSupportData O ell c PX PY PZ) : Prop :=
    -- openExact
    (PreservesFiniteLimits record.openExtension ∧ PreservesFiniteColimits record.openExtension) ∧
    -- openTranspose
    (∀ n, (record.openImage.inverseEvaluation n).hom =
      (mateEquiv record.openAdjunction (record.levelOpenAdjunction n)
        (.mk _ _ _ _ (record.openEvaluation n).inv))) ∧
    -- derivedOpenTranspose
    (∀ P K
      (h : (record.openExtension.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      record.derivedOpenAdjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        (record.openFactors.hom.app P ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map ((record.openAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P K h) ≫
        record.openDerived.system.inverseFactors.inv.app K) ∧
    -- levelDerivedOpenTranspose
    (∀ n P K
      (h : ((record.levelOpen n).mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      (record.levelDerivedOpenAdjunction n).homEquiv
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        ((record.levelOpenFactors n).hom.app P ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map
        (((record.levelOpenAdjunction n).mapHomologicalComplex (.up ℤ)).homEquiv P K h) ≫
          (record.openDerived.level n).inverseFactors.inv.app K) ∧
    -- openDerivedEvaluation_rep
    (∀ n K,
      (record.openDerivedEvaluation n).hom.app (DerivedCategory.Q.obj K) ≫
        (record.levelDerivedOpen n).map ((PX.evaluationFactors n).hom.app K) ≫
        (record.levelOpenFactors n).hom.app
          (((coefficientEvaluation (J := Scheme.ProEt.topology X)
            (O := O) (ell := ell) n).mapHomologicalComplex (.up ℤ)).obj K) =
      (PZ.evaluation n).map (record.openFactors.hom.app K) ≫
        (PZ.evaluationFactors n).hom.app
          ((record.openExtension.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (record.openEvaluation n) (.up ℤ)).hom.app K))

/-- The specified data and canonical coherence of `ExceptionalProCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalProCompactSupport :=
  { record : ExceptionalProCompactSupportData O ell c PX PY PZ //
    ExceptionalProCompactSupportCoherence O ell c PX PY PZ record }

/-- Site comparison with the actual system unit and counit.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 09B1
(blueprint: lem-sf-exceptional-system-transport). -/
structure ExceptionalSystemSiteComparison (T : Scheme.{u})
    (P : StrictEtaleEvaluation T O ell) where
  proEvaluation : ExceptionalProEvaluation T O ell
  ordinary : CoefficientSystemOrdinaryImage (J := T.smallEtaleTopology)
    (K := Scheme.ProEt.topology T) O ell _ _ (Scheme.proEtaleSiteComparison T)
  image : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
    (J := T.smallEtaleTopology)
    (K := Scheme.ProEt.topology T) O ell _ _ (Scheme.proEtaleSiteComparison T)
    ordinary P proEvaluation

variable {O ell c}

/-- Bounded-below systems with levelwise etale origin; the bound is uniform in the level.
Source: Zheng Lemma 4.10; Stacks 09B1
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalSystemSiteComparison.origin {T : Scheme.{u}}
    {P : StrictEtaleEvaluation T O ell} (C : ExceptionalSystemSiteComparison O ell T P) :
    ObjectProperty (DerivedCategory (CoefficientSystem (J := Scheme.ProEt.topology T) O ell)) :=
  fun M ↦ (∃ a : ℤ, M.IsGE a) ∧ ∀ n, ∃ N : DerivedCategory (strictEtaleLevel T O ell n),
    (∃ a : ℤ, N.IsGE a) ∧ Nonempty ((C.image.level n).inverse.obj N ≅
      (C.proEvaluation.evaluation n).obj M)

/-- The equivalence and normalization clauses, on the prescribed full classes.
Source: Zheng Lemma 4.10 and Stacks 09B1
(blueprint: lem-sf-exceptional-system-transport). -/
structure ExceptionalSystemSiteEquivalence {T : Scheme.{u}}
    {P : StrictEtaleEvaluation T O ell} (C : ExceptionalSystemSiteComparison O ell T P) : Prop where
  inverseBound : ∀ (a : ℤ) M, M.IsGE a → (C.image.system.inverse.obj M).IsGE a
  directBound : ∀ (a : ℤ) M, M.IsGE a → (C.image.system.direct.obj M).IsGE a
  unit : ∀ M, (∃ a : ℤ, M.IsGE a) → IsIso (C.image.system.adjunction.unit.app M)
  counit : ∀ M, C.origin M → IsIso (C.image.system.adjunction.counit.app M)
  inverseOrigin : ∀ M, (∃ a : ℤ, M.IsGE a) → C.origin (C.image.system.inverse.obj M)
  inverseNormalized : ∀ M, (∃ a : ℤ, M.IsGE a) →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2} O ell P M →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      O ell C.proEvaluation (C.image.system.inverse.obj M)
  directNormalized : ∀ M, C.origin M →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2} O ell C.proEvaluation M →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2} O ell P (C.image.system.direct.obj M)

/-- A system pullback square fixed on underlying sheaves and on complex representatives.
It includes the ordinary evaluation square, so the derived square is constructed before
finite evaluation. Source: Zheng Construction 4.1; Stacks 099R and 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
structure ExceptionalSystemPullbackSquareData
    {T S : Scheme.{u}} (g : T ⟶ S)
    {PT : StrictEtaleEvaluation T O ell} {PS : StrictEtaleEvaluation S O ell}
    (CT : ExceptionalSystemSiteComparison O ell T PT)
    (CS : ExceptionalSystemSiteComparison O ell S PS)
    (E : StrictEtaleOrdinaryImage O ell g) (P : ExceptionalProOrdinaryImage O ell g)
    (ED : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := S.smallEtaleTopology) (K := T.smallEtaleTopology) O ell _ _ _ E PS PT)
    (PD : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T) O ell _ _ _ P
      CS.proEvaluation CT.proEvaluation) where
  ordinary : CS.ordinary.inverse ⋙ P.inverse ≅ E.inverse ⋙ CT.ordinary.inverse
  level : ∀ n, (CS.ordinary.lift n).modules ⋙ (P.lift n).modules ≅
    (E.lift n).modules ⋙ (CT.ordinary.lift n).modules
  square : CS.image.system.inverse ⋙ PD.system.inverse ≅
    ED.system.inverse ⋙ CT.image.system.inverse
  derivedLevel : ∀ n, (CS.image.level n).inverse ⋙ (PD.level n).inverse ≅
    (ED.level n).inverse ⋙ (CT.image.level n).inverse

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalSystemPullbackSquareCoherence
    {T S : Scheme.{u}} (g : T ⟶ S)
    {PT : StrictEtaleEvaluation T O ell} {PS : StrictEtaleEvaluation S O ell}
    (CT : ExceptionalSystemSiteComparison O ell T PT)
    (CS : ExceptionalSystemSiteComparison O ell S PS)
    (E : StrictEtaleOrdinaryImage O ell g) (P : ExceptionalProOrdinaryImage O ell g)
    (ED : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := S.smallEtaleTopology) (K := T.smallEtaleTopology) O ell _ _ _ E PS PT)
    (PD : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T) O ell _ _ _ P
      CS.proEvaluation CT.proEvaluation)
    (record : ExceptionalSystemPullbackSquareData g CT CS E P ED PD) : Prop :=
    -- underlying
    (∀ n (M : strictEtaleLevel S O ell n),
    (coefficientUnderlying (J := Scheme.ProEt.topology T) O ell n).map
        ((record.level n).hom.app M) ≫
      (CT.ordinary.lift n).moduleUnderlying.hom.app ((E.lift n).modules.obj M) ≫
      (ProEtale.comparisonCoefficientPullback (Type (u + 1)) T).map
        ((E.lift n).moduleUnderlying.hom.app M) =
    (P.lift n).moduleUnderlying.hom.app ((CS.ordinary.lift n).modules.obj M) ≫
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1))).map
        ((CS.ordinary.lift n).moduleUnderlying.hom.app M) ≫
      (ProEtale.comparisonCoefficientPullbackIso (Type (u + 1)) g).inv.app
        ((coefficientUnderlying (J := S.smallEtaleTopology) O ell n).obj M)) ∧
    -- ordinaryEvaluation
    (∀ n (M : strictEtaleCoefficientSystem S O ell),
    (coefficientEvaluation (J := Scheme.ProEt.topology T) (O := O) (ell := ell) n).map
        (record.ordinary.hom.app M) ≫
      (CT.ordinary.inverseEvaluation n).hom.app (E.inverse.obj M) ≫
      (CT.ordinary.lift n).modules.map ((E.inverseEvaluation n).hom.app M) =
    (P.inverseEvaluation n).hom.app (CS.ordinary.inverse.obj M) ≫
      (P.lift n).modules.map ((CS.ordinary.inverseEvaluation n).hom.app M) ≫
      (record.level n).hom.app (M.level n)) ∧
    -- levelFactors
    (∀ n (H : CochainComplex (strictEtaleLevel S O ell n) ℤ),
    (record.derivedLevel n).hom.app (DerivedCategory.Q.obj H) ≫
      (CT.image.level n).inverse.map ((ED.level n).inverseFactors.hom.app H) ≫
      (CT.image.level n).inverseFactors.hom.app
        (((E.lift n).modules.mapHomologicalComplex (.up ℤ)).obj H) =
    (PD.level n).inverse.map ((CS.image.level n).inverseFactors.hom.app H) ≫
      (PD.level n).inverseFactors.hom.app
        (((CS.ordinary.lift n).modules.mapHomologicalComplex (.up ℤ)).obj H) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (record.level n) (.up ℤ)).hom.app H)) ∧
    -- evaluation
    (∀ n M,
    (CT.proEvaluation.evaluation n).map (record.square.hom.app M) ≫
      (CT.image.inverseEvaluation n).hom.app (ED.system.inverse.obj M) ≫
      (CT.image.level n).inverse.map ((ED.inverseEvaluation n).hom.app M) =
    (PD.inverseEvaluation n).hom.app (CS.image.system.inverse.obj M) ≫
      (PD.level n).inverse.map ((CS.image.inverseEvaluation n).hom.app M) ≫
      (record.derivedLevel n).hom.app ((PS.evaluation n).obj M)) ∧
    -- factors
    (∀ H : CochainComplex (strictEtaleCoefficientSystem S O ell) ℤ,
    record.square.hom.app (DerivedCategory.Q.obj H) ≫
      CT.image.system.inverse.map (ED.system.inverseFactors.hom.app H) ≫
      CT.image.system.inverseFactors.hom.app
        ((E.inverse.mapHomologicalComplex (.up ℤ)).obj H) =
    PD.system.inverse.map (CS.image.system.inverseFactors.hom.app H) ≫
      PD.system.inverseFactors.hom.app
        ((CS.ordinary.inverse.mapHomologicalComplex (.up ℤ)).obj H) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex record.ordinary (.up ℤ)).hom.app H))

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalSystemPullbackSquare
    {T S : Scheme.{u}} (g : T ⟶ S)
    {PT : StrictEtaleEvaluation T O ell} {PS : StrictEtaleEvaluation S O ell}
    (CT : ExceptionalSystemSiteComparison O ell T PT)
    (CS : ExceptionalSystemSiteComparison O ell S PS)
    (E : StrictEtaleOrdinaryImage O ell g) (P : ExceptionalProOrdinaryImage O ell g)
    (ED : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := S.smallEtaleTopology) (K := T.smallEtaleTopology) O ell _ _ _ E PS PT)
    (PD : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T) O ell _ _ _ P
      CS.proEvaluation CT.proEvaluation) :=
  { record : ExceptionalSystemPullbackSquareData g CT CS E P ED PD //
    ExceptionalSystemPullbackSquareCoherence g CT CS E P ED PD record }

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalSystemPullbackSquare.ordinary
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PT : StrictEtaleEvaluation T O ell} {PS : StrictEtaleEvaluation S O ell}
    {CT : ExceptionalSystemSiteComparison O ell T PT}
    {CS : ExceptionalSystemSiteComparison O ell S PS}
    {E : StrictEtaleOrdinaryImage O ell g} {P : ExceptionalProOrdinaryImage O ell g}
    {ED : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := S.smallEtaleTopology) (K := T.smallEtaleTopology) O ell _ _ _ E PS PT}
    {PD : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T) O ell _ _ _ P
      CS.proEvaluation CT.proEvaluation}
    (record : ExceptionalSystemPullbackSquare g CT CS E P ED PD) :=
  record.val.ordinary

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalSystemPullbackSquare.level
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PT : StrictEtaleEvaluation T O ell} {PS : StrictEtaleEvaluation S O ell}
    {CT : ExceptionalSystemSiteComparison O ell T PT}
    {CS : ExceptionalSystemSiteComparison O ell S PS}
    {E : StrictEtaleOrdinaryImage O ell g} {P : ExceptionalProOrdinaryImage O ell g}
    {ED : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := S.smallEtaleTopology) (K := T.smallEtaleTopology) O ell _ _ _ E PS PT}
    {PD : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T) O ell _ _ _ P
      CS.proEvaluation CT.proEvaluation}
    (record : ExceptionalSystemPullbackSquare g CT CS E P ED PD) :=
  record.val.level

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalSystemPullbackSquare.square
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PT : StrictEtaleEvaluation T O ell} {PS : StrictEtaleEvaluation S O ell}
    {CT : ExceptionalSystemSiteComparison O ell T PT}
    {CS : ExceptionalSystemSiteComparison O ell S PS}
    {E : StrictEtaleOrdinaryImage O ell g} {P : ExceptionalProOrdinaryImage O ell g}
    {ED : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := S.smallEtaleTopology) (K := T.smallEtaleTopology) O ell _ _ _ E PS PT}
    {PD : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T) O ell _ _ _ P
      CS.proEvaluation CT.proEvaluation}
    (record : ExceptionalSystemPullbackSquare g CT CS E P ED PD) :=
  record.val.square

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalSystemPullbackSquare.derivedLevel
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PT : StrictEtaleEvaluation T O ell} {PS : StrictEtaleEvaluation S O ell}
    {CT : ExceptionalSystemSiteComparison O ell T PT}
    {CS : ExceptionalSystemSiteComparison O ell S PS}
    {E : StrictEtaleOrdinaryImage O ell g} {P : ExceptionalProOrdinaryImage O ell g}
    {ED : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := S.smallEtaleTopology) (K := T.smallEtaleTopology) O ell _ _ _ E PS PT}
    {PD : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology S) (K := Scheme.ProEt.topology T) O ell _ _ _ P
      CS.proEvaluation CT.proEvaluation}
    (record : ExceptionalSystemPullbackSquare g CT CS E P ED PD) :=
  record.val.derivedLevel

/-- The actual pro-etale compact-support operation, formed on derived systems.
Source: Zheng Construction 5.15
(blueprint: lem-sf-exceptional-system-transport). -/
def exceptionalProSupport {PX : ExceptionalProEvaluation X O ell}
    {PY : ExceptionalProEvaluation Y O ell} {PZ : ExceptionalProEvaluation c.Z O ell}
    (P : ExceptionalProCompactSupport O ell c PX PY PZ) :=
  P.val.derivedOpen ⋙ P.val.properDerived.system.direct

/-- Its actual finite evaluation, obtained from open and proper evaluation isomorphisms.
Source: Zheng Lemma 5.16
(blueprint: lem-sf-exceptional-system-transport). -/
def exceptionalProSupportEvaluation {PX : ExceptionalProEvaluation X O ell}
    {PY : ExceptionalProEvaluation Y O ell} {PZ : ExceptionalProEvaluation c.Z O ell}
    (P : ExceptionalProCompactSupport O ell c PX PY PZ) (n : ℕ) :
    exceptionalProSupport P ⋙ PY.evaluation n ≅
      PX.evaluation n ⋙ (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct) :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (P.val.properDerived.directEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (P.val.openDerivedEvaluation n) _ ≪≫ Functor.associator _ _ _

/-- Proper and open comparison data, whose mate equations fix the canonical maps.
Source: Zheng Construction 5.15; Stacks 0B65; blueprint system-transport step 3
(blueprint: lem-sf-exceptional-system-transport). -/
structure ExceptionalSystemCompactificationComparisonData
    (S : StrictEtaleCompactSupport O ell c)
    (CX : ExceptionalSystemSiteComparison O ell X S.PX)
    (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
    (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation) where
  properSquare : ExceptionalSystemPullbackSquare c.g CZ CY
    S.properImage P.val.properImage S.properDerived P.val.properDerived
  openSquare : ExceptionalSystemPullbackSquare c.i CX CZ
    S.openImage P.val.openImage S.openDerived P.val.openDerived
  openComparison : S.derivedOpen ⋙ CZ.image.system.inverse ≅
    CX.image.system.inverse ⋙ P.val.derivedOpen
  levelOpenComparison : ∀ n, S.levelDerivedOpen n ⋙ (CZ.image.level n).inverse ≅
    (CX.image.level n).inverse ⋙ P.val.levelDerivedOpen n

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalSystemCompactificationComparisonCoherence
    (S : StrictEtaleCompactSupport O ell c)
    (CX : ExceptionalSystemSiteComparison O ell X S.PX)
    (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
    (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
    (record : ExceptionalSystemCompactificationComparisonData S CX CY CZ P) : Prop :=
    -- openMate
    ((mateEquiv S.derivedOpenAdjunction P.val.derivedOpenAdjunction
    (.mk _ _ _ _ record.openComparison.inv)) = record.openSquare.square.inv) ∧
    -- levelOpenMate
    (∀ n,
    (mateEquiv (S.levelDerivedOpenAdjunction n) (P.val.levelDerivedOpenAdjunction n)
      (.mk _ _ _ _ (record.levelOpenComparison n).inv)) =
      (record.openSquare.derivedLevel n).inv) ∧
    -- openEvaluation
    (∀ n M,
    (CZ.proEvaluation.evaluation n).map (record.openComparison.hom.app M) ≫
      (P.val.openDerivedEvaluation n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n).map ((CX.image.inverseEvaluation n).hom.app M) =
    (CZ.image.inverseEvaluation n).hom.app (S.derivedOpen.obj M) ≫
      (CZ.image.level n).inverse.map ((S.openDerivedEvaluation n).hom.app M) ≫
      (record.levelOpenComparison n).hom.app ((S.PX.evaluation n).obj M))

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalSystemCompactificationComparison
    (S : StrictEtaleCompactSupport O ell c)
    (CX : ExceptionalSystemSiteComparison O ell X S.PX)
    (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
    (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation) :=
  { record : ExceptionalSystemCompactificationComparisonData S CX CY CZ P //
    ExceptionalSystemCompactificationComparisonCoherence S CX CY CZ P record }

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalSystemCompactificationComparison.properSquare
    {S : StrictEtaleCompactSupport O ell c}
    {CX : ExceptionalSystemSiteComparison O ell X S.PX}
    {CY : ExceptionalSystemSiteComparison O ell Y S.PY}
    {CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ}
    {P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation}
    (record : ExceptionalSystemCompactificationComparison S CX CY CZ P) :=
  record.val.properSquare

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalSystemCompactificationComparison.openSquare
    {S : StrictEtaleCompactSupport O ell c}
    {CX : ExceptionalSystemSiteComparison O ell X S.PX}
    {CY : ExceptionalSystemSiteComparison O ell Y S.PY}
    {CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ}
    {P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation}
    (record : ExceptionalSystemCompactificationComparison S CX CY CZ P) :=
  record.val.openSquare

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalSystemCompactificationComparison.openComparison
    {S : StrictEtaleCompactSupport O ell c}
    {CX : ExceptionalSystemSiteComparison O ell X S.PX}
    {CY : ExceptionalSystemSiteComparison O ell Y S.PY}
    {CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ}
    {P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation}
    (record : ExceptionalSystemCompactificationComparison S CX CY CZ P) :=
  record.val.openComparison

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
abbrev ExceptionalSystemCompactificationComparison.levelOpenComparison
    {S : StrictEtaleCompactSupport O ell c}
    {CX : ExceptionalSystemSiteComparison O ell X S.PX}
    {CY : ExceptionalSystemSiteComparison O ell Y S.PY}
    {CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ}
    {P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation}
    (record : ExceptionalSystemCompactificationComparison S CX CY CZ P) :=
  record.val.levelOpenComparison

variable {S : StrictEtaleCompactSupport O ell c}
  {CX : ExceptionalSystemSiteComparison O ell X S.PX}
  {CY : ExceptionalSystemSiteComparison O ell Y S.PY}
  {CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ}
  {P : ExceptionalProCompactSupport O ell c
    CX.proEvaluation CY.proEvaluation CZ.proEvaluation}

/-- The proper derived mate followed by open comparison, as one actual system map.
Source: blueprint system-transport steps 3--4; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
def exceptionalSystemComparison
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P) :
    S.functor ⋙ CY.image.system.inverse ⟶ CX.image.system.inverse ⋙ exceptionalProSupport P :=
  (Functor.associator _ _ _).hom ≫
    whiskerLeft S.derivedOpen
      (mateEquiv S.properDerived.system.adjunction P.val.properDerived.system.adjunction
        (.mk _ _ _ _ R.properSquare.square.hom)) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight R.openComparison.hom P.val.properDerived.system.direct ≫
    (Functor.associator _ _ _).hom

/-- The comparison on origin systems includes the actual site counit at the source.
Source: blueprint system-transport step 4
(blueprint: lem-sf-exceptional-system-transport). -/
def exceptionalSystemOriginComparison
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P) :
    CX.image.system.direct ⋙ S.functor ⋙ CY.image.system.inverse ⟶ exceptionalProSupport P :=
  whiskerLeft CX.image.system.direct (exceptionalSystemComparison R) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight CX.image.system.adjunction.counit (exceptionalProSupport P) ≫
    (Functor.leftUnitor _).hom

/-- The transported right functor is the stated composite, on whole derived systems.
Source: Zheng Lemma 5.22; blueprint system-transport step 5
(blueprint: lem-sf-exceptional-system-transport). -/
def exceptionalSystemRight (G : StrictEtaleExceptionalAdjoint O ell c S)
    (CX : ExceptionalSystemSiteComparison O ell X S.PX)
    (CY : ExceptionalSystemSiteComparison O ell Y S.PY) :=
  CY.image.system.direct ⋙ G.right ⋙ CX.image.system.inverse

/-- The finite proper/open map, with the very same mate convention as on systems.
Source: Stacks 0B65; blueprint system-transport steps 3--6
(blueprint: lem-sf-exceptional-system-transport). -/
def exceptionalSystemLevelComparison
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P) (n : ℕ) :
    S.levelFunctor n ⋙ (CY.image.level n).inverse ⟶
      (CX.image.level n).inverse ⋙
        (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct) :=
  (Functor.associator _ _ _).hom ≫
    whiskerLeft (S.levelDerivedOpen n)
      (mateEquiv (S.properDerived.level n).adjunction (P.val.properDerived.level n).adjunction
        (.mk _ _ _ _ (R.properSquare.derivedLevel n).hom)) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (R.levelOpenComparison n).hom (P.val.properDerived.level n).direct ≫
    (Functor.associator _ _ _).hom

/-- The finite origin comparison also uses the source site's actual counit.
Source: blueprint system-transport steps 4--6
(blueprint: lem-sf-exceptional-system-transport). -/
def exceptionalSystemLevelOriginComparison
    (R : ExceptionalSystemCompactificationComparison S CX CY CZ P) (n : ℕ) :
    (CX.image.level n).direct ⋙ S.levelFunctor n ⋙ (CY.image.level n).inverse ⟶
      P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct :=
  whiskerLeft (CX.image.level n).direct (exceptionalSystemLevelComparison R n) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (CX.image.level n).adjunction.counit _ ≫ (Functor.leftUnitor _).hom

/-- Finite etale origin, retaining the bounded-below condition at each positive level.
Source: Stacks 09B1; blueprint system-transport step 6
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalSystemSiteComparison.levelOrigin {T : Scheme.{u}}
    {PE : StrictEtaleEvaluation T O ell} (C : ExceptionalSystemSiteComparison O ell T PE)
    (n : ℕ) :
    ObjectProperty (DerivedCategory
      (coefficientLevelModules (J := Scheme.ProEt.topology T) O ell n)) :=
  fun M ↦ (∃ a : ℤ, M.IsGE a) ∧ ∃ N : DerivedCategory (strictEtaleLevel T O ell n),
    (∃ a : ℤ, N.IsGE a) ∧ Nonempty ((C.image.level n).inverse.obj N ≅ M)

end AlgebraicGeometry

namespace CategoryTheory
universe a b x y av bv xv yv

/-- The actual restricted adjunction with its Hom-chain normalization. The displayed
transpose equation is the forward Hom-chain formula with the source site counit
composed on the left; this avoids choosing any inverse before proving invertibility.
It fixes both the unit and the counit on whole objects of the full subcategories.
Source: Stacks 0037; blueprint system-transport steps 5--6
(blueprint: lem-sf-exceptional-system-transport). -/
structure ExceptionalOriginAdjunction
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {X : Type x} [Category.{xv} X] {Y : Type y} [Category.{yv} Y]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {CX : A ⥤ X} {VX : X ⥤ A} (adjX : CX ⊣ VX)
    {CY : B ⥤ Y} {VY : Y ⥤ B} (adjY : CY ⊣ VY)
    (FP : X ⥤ Y) (PX : ObjectProperty X) (PY : ObjectProperty Y)
    (kappa : VX ⋙ F ⋙ CY ⟶ FP) where
  leftStable : ∀ M, PX M → PY (FP.obj M)
  rightStable : ∀ N, PY N → PX ((VY ⋙ G ⋙ CX).obj N)
  adjunction :
    PY.lift (PX.ι ⋙ FP) (fun M ↦ leftStable M.obj M.property) ⊣
      PX.lift (PY.ι ⋙ (VY ⋙ G ⋙ CX)) (fun N ↦ rightStable N.obj N.property)
  transpose : ∀ M N (h :
      (PY.lift (PX.ι ⋙ FP) (fun M ↦ leftStable M.obj M.property)).obj M ⟶ N),
    CX.map (adj.homEquiv (VX.obj M.obj) (VY.obj N.obj)
      (adjY.unit.app (F.obj (VX.obj M.obj)) ≫ VY.map (kappa.app M.obj ≫ h.hom))) =
    adjX.counit.app M.obj ≫ (adjunction.homEquiv M N h).hom

end CategoryTheory

namespace AlgebraicGeometry
variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}

/-- Multiplication by constants on pro-etale strict systems, with its unique exact
localization on complexes. This is the scalar action used for linearity below.
Source: Zheng Construction 4.1 and Proposition 2.29(2)
(blueprint: lem-sf-exceptional-system-transport). -/
structure ExceptionalProScalarAction (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) where
  ordinary : O → (𝟭 (CoefficientSystem (J := Scheme.ProEt.topology T) O ell) ⟶ 𝟭 _)
  derived : O →
    (𝟭 (DerivedCategory (CoefficientSystem (J := Scheme.ProEt.topology T) O ell)) ⟶ 𝟭 _)
  ordinaryNormalized : ∀ r M n (U : T.ProEtᵒᵖ) (x : (M.level n).val.obj U),
    (((ordinary r).app M).app n).val.app U x =
      ((toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U
          (Ideal.Quotient.mk _ r)) • x
  representative : ∀ r K,
    (derived r).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (((ordinary r).mapHomologicalComplex (.up ℤ)).app K)

/-- Right evaluation before the final target-site direct-image identification.
Source: Zheng Lemma 5.22; blueprint system-transport steps 6--7
(blueprint: lem-sf-exceptional-system-transport). -/
def exceptionalSystemRightEtaleEvaluation (G : StrictEtaleExceptionalAdjoint O ell c S)
    (CX : ExceptionalSystemSiteComparison O ell X S.PX)
    (CY : ExceptionalSystemSiteComparison O ell Y S.PY) (n : ℕ) :
    exceptionalSystemRight G CX CY ⋙ CX.proEvaluation.evaluation n ≅
      CY.image.system.direct ⋙ S.PY.evaluation n ⋙ G.levelRight n ⋙ (CX.image.level n).inverse :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (CX.image.inverseEvaluation n) ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (G.evaluation n) _ ≪≫
        Functor.associator _ _ _)

/-- Right evaluation is the canonical composite of the three recorded evaluations.
Source: Zheng Lemma 5.22; blueprint system-transport step 6
(blueprint: lem-sf-exceptional-system-transport). -/
def exceptionalSystemRightEvaluation (G : StrictEtaleExceptionalAdjoint O ell c S)
    (CX : ExceptionalSystemSiteComparison O ell X S.PX)
    (CY : ExceptionalSystemSiteComparison O ell Y S.PY) (n : ℕ) :
    exceptionalSystemRight G CX CY ⋙ CX.proEvaluation.evaluation n ≅
      CY.proEvaluation.evaluation n ⋙
        (CY.image.level n).direct ⋙ G.levelRight n ⋙ (CX.image.level n).inverse :=
  exceptionalSystemRightEtaleEvaluation G CX CY n ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (CY.image.directEvaluation n) _ ≪≫ Functor.associator _ _ _

variable (G : StrictEtaleExceptionalAdjoint O ell c S)
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)
  (P : ExceptionalProCompactSupport O ell c
    CX.proEvaluation CY.proEvaluation CZ.proEvaluation)
  (R : ExceptionalSystemCompactificationComparison S CX CY CZ P)

/-- The adjunction, finite evaluations, quotient transposes, exactness and uniform bound
of system transport. All geometric data are the previously specified constructions.
Source: Zheng Lemmas 4.10 and 5.22, Proposition 5.24; Stacks 0037, 09B1 and 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
structure ExceptionalSystemTransportData where
  siteX : ExceptionalSystemSiteEquivalence CX
  siteY : ExceptionalSystemSiteEquivalence CY
  siteZ : ExceptionalSystemSiteEquivalence CZ
  systemAdjunction : ExceptionalOriginAdjunction G.adjunction
    CX.image.system.adjunction CY.image.system.adjunction
    (exceptionalProSupport P) CX.origin CY.origin (exceptionalSystemOriginComparison R)
  finiteAdjunction : ∀ n, ExceptionalOriginAdjunction (G.levelAdjunction n)
    (CX.image.level n).adjunction (CY.image.level n).adjunction
    (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct)
    (CX.levelOrigin n) (CY.levelOrigin n) (exceptionalSystemLevelOriginComparison R n)
  evaluationOriginX : ∀ n M, CX.origin M →
    CX.levelOrigin n ((CX.proEvaluation.evaluation n).obj M)
  evaluationOriginY : ∀ n M, CY.origin M →
    CY.levelOrigin n ((CY.proEvaluation.evaluation n).obj M)
  [leftAdditive : (exceptionalProSupport P).Additive]
  [rightAdditive : (exceptionalSystemRight G CX CY).Additive]
  [leftShift : (exceptionalProSupport P).CommShift ℤ]
  [rightShift : (exceptionalSystemRight G CX CY).CommShift ℤ]
  scalarX : ExceptionalProScalarAction X O ell
  scalarY : ExceptionalProScalarAction Y O ell

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalSystemTransportCoherence
    (record : ExceptionalSystemTransportData G CX CY CZ P R) : Prop :=
    -- comparisonIso
    (∀ M, (∃ a : ℤ, M.IsGE a) →
    IsIso ((exceptionalSystemComparison R).app M)) ∧
    -- originComparisonIso
    (∀ M, CX.origin M →
    IsIso ((exceptionalSystemOriginComparison R).app M)) ∧
    -- comparisonEvaluation
    (∀ n M,
    (CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison R).app M) ≫
      (exceptionalProSupportEvaluation P n).hom.app (CX.image.system.inverse.obj M) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((CX.image.inverseEvaluation n).hom.app M) =
    (CY.image.inverseEvaluation n).hom.app (S.functor.obj M) ≫
      (CY.image.level n).inverse.map ((S.evaluation n).hom.app M) ≫
      (exceptionalSystemLevelComparison R n).app ((S.PX.evaluation n).obj M)) ∧
    -- unitEvaluation
    (∀ n M,
    (CX.proEvaluation.evaluation n).map (record.systemAdjunction.adjunction.unit.app M).hom ≫
      (exceptionalSystemRightEvaluation G CX CY n).hom.app
        ((exceptionalProSupport P).obj M.obj) ≫
      ((CY.image.level n).direct ⋙ G.levelRight n ⋙ (CX.image.level n).inverse).map
        ((exceptionalProSupportEvaluation P n).hom.app M.obj) =
    ((record.finiteAdjunction n).adjunction.unit.app
      ⟨(CX.proEvaluation.evaluation n).obj M.obj,
        record.evaluationOriginX n M.obj M.property⟩).hom) ∧
    -- counitEvaluation
    (∀ n N,
    (exceptionalProSupportEvaluation P n).hom.app
        ((exceptionalSystemRight G CX CY).obj N.obj) ≫
      (P.val.levelDerivedOpen n ⋙ (P.val.properDerived.level n).direct).map
        ((exceptionalSystemRightEvaluation G CX CY n).hom.app N.obj) ≫
      ((record.finiteAdjunction n).adjunction.counit.app
        ⟨(CY.proEvaluation.evaluation n).obj N.obj,
          record.evaluationOriginY n N.obj N.property⟩).hom =
    (CY.proEvaluation.evaluation n).map (record.systemAdjunction.adjunction.counit.app N).hom) ∧
    -- quotientTransition
    (∀ {m n : ℕ} (h : n ≤ m) N,
    (CX.proEvaluation.scalar h).derived.map
        ((exceptionalSystemRightEtaleEvaluation G CX CY m).hom.app N) ≫
      (CX.image.derivedTensor h).inv.app
        ((G.levelRight m).obj ((S.PY.evaluation m).obj (CY.image.system.direct.obj N))) ≫
      (CX.image.level n).inverse.map
        ((G.quotientComparison h).hom.app
          ((S.PY.evaluation m).obj (CY.image.system.direct.obj N))) ≫
      (CX.image.level n).inverse.map ((G.levelRight n).map
        (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
          ((S.PY.transition h).app (CY.image.system.direct.obj N)))) =
    ((CX.proEvaluation.scalar h).derivedAdj.homEquiv _ _).symm
        ((CX.proEvaluation.transition h).app ((exceptionalSystemRight G CX CY).obj N)) ≫
      (exceptionalSystemRightEtaleEvaluation G CX CY n).hom.app N) ∧
    -- leftExact
    (@Functor.IsTriangulated _ _ _ _ _ _
      (exceptionalProSupport P) record.leftShift _ _ _ _ _ _ _ _) ∧
    -- rightExact
    (@Functor.IsTriangulated _ _ _ _ _ _
      (exceptionalSystemRight G CX CY) record.rightShift _ _ _ _ _ _ _ _) ∧
    -- leftLinear
    (∀ r M, (exceptionalProSupport P).map ((record.scalarX.derived r).app M) =
    (record.scalarY.derived r).app ((exceptionalProSupport P).obj M)) ∧
    -- rightLinear
    (∀ r N, (exceptionalSystemRight G CX CY).map ((record.scalarY.derived r).app N) =
    (record.scalarX.derived r).app ((exceptionalSystemRight G CX CY).obj N)) ∧
    -- normalized
    (∀ N, CY.origin N →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2} O ell CY.proEvaluation N →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2} O ell CX.proEvaluation
      ((exceptionalSystemRight G CX CY).obj N)) ∧
    -- lowerBound
    (∃ c_f : ℕ, ∀ (a : ℤ) N, CY.origin N → N.IsGE a →
    ((exceptionalSystemRight G CX CY).obj N).IsGE (a - c_f))

/-- Canonical construction data and its normalization equations.
Source: Zheng Construction 4.1, Lemma 4.10 and Lemma 5.22; Stacks 0B65
(blueprint: lem-sf-exceptional-system-transport). -/
def ExceptionalSystemTransport :=
  { record : ExceptionalSystemTransportData G CX CY CZ P R //
    ExceptionalSystemTransportCoherence G CX CY CZ P R record }

end AlgebraicGeometry
