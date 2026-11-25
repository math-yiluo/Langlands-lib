/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction

/-!
# Interfaces for compact support on strict varying-coefficient towers

Source: Stacks Project, Tags 0F7J and 03S5; blueprint main-20261015,
`proposition-sp-tower-geometric`, Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus).

All categories are ordinary derived categories. Natural-number level n means exponent
n+1. The section-preserving presentation in the recorded shriek-level theorem is used
only to transport its constructed operations to the recorded strict tower category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Reuse the inherited coefficient-universe sheafification instead of small-site transport.
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The derived equivalence induced by the dependency's section-preserving realization.
Source: blueprint, strict section model (blueprint: lem-sp-coefficient-tower-shriek-calculus).
-/
def realization (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (a : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T a ≌ SpTowerShriek.D l E T := by
  letI := a.hasDerived
  letI := b.realizationAdditive T
  exact (b.realization T).mapDerivedCategory

/-- Compact support is precisely the recorded open/proper composite, in the original
strict tower coordinates. Source: blueprint, F_h = Rp_* j_!
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def compactSupport (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (a : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    spDerivedCoefficientTowers l E X (a X) ⥤ spDerivedCoefficientTowers l E Y (a Y) :=
  (realization l E b X (a X)).functor ⋙ SpTowerShriek.F l E b o c ⋙
    (realization l E b Y (a Y)).inverse

/-- The actual quotient homomorphism O_E/ell^(n+1) -> O_E/ell^(m+1).
Source: blueprint, clause (3) (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def quotient {m n : ℕ} (h : m ≤ n) : SpTowerShriek.R l E n →+* SpTowerShriek.R l E m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The existing strict-system scalar functor in the tower abelianness interface.
Source: blueprint, clause (3) (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
abbrev systemScalar (T : Scheme.{u}) (a : SpCoefficientTowersAbelian l E T)
    {m n : ℕ} (h : m ≤ n) :=
  SheafOfModules.systemDerivedTensor.{u + 1, u, u + 1}
    a.scalar (spCoefficientCommRings l E T) h

/-- Ordinary coefficient restriction, in the dependency's strict-system coordinates.
Source: blueprint, clause (3) (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
abbrev systemRestriction (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :=
  SheafOfModules.systemRestriction.{u + 1, u, u + 1} (spCoefficientCommRings l E T) h

-- These operation interfaces do not use constructor injectivity or SizeOf equations.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A coordinate identification of the two canonical scalar functors. The ordinary
restriction identification is the identity on every section, and the scalar comparison
preserves the normalized adjunction. Thus it cannot introduce a scalar automorphism.
Source: blueprint, reduction normalization
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
structure ScalarCoordinates (T : Scheme.{u}) (a : SpCoefficientTowersAbelian l E T)
    {m n : ℕ} (h : m ≤ n) where
  restriction : systemRestriction l E T h ≅
    SheafOfModules.restrictScalars
      ((sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleConstantRingMap (T := T) (quotient l E h)))
  restriction_sections : ∀ (M : proEtaleRingModules T
      (proEtaleConstantRing T (SpTowerShriek.R l E m))) (U : T.ProEtᵒᵖ)
      (x : ((systemRestriction l E T h).obj M).val.obj U),
    HEq (((restriction.hom.app M).val.app U) x) x
  scalar : systemScalar l E T a h ≅ scalarExtensionFunctor (quotient l E h) T
  unit : ∀ M : proEtaleDerivedCategory T (SpTowerShriek.R l E n),
    (SheafOfModules.systemDerivedTensorAdj.{u + 1, u, u + 1}
      a.scalar (spCoefficientCommRings l E T) h).unit.app M ≫
      (systemRestriction l E T h).mapDerivedCategory.map (scalar.hom.app M) ≫
      (Functor.mapDerivedCategoryNatIso restriction).hom.app
        ((scalarExtensionFunctor (quotient l E h) T).obj M) =
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotient l E h))).unit.app M

/-- The reduction map in intrinsic constant-ring coordinates, obtained from the recorded
reduction by the uniquely adjunction-normalized scalar comparison.
Source: blueprint, r^C_(n,m) (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def reduction (T : Scheme.{u}) (a : SpCoefficientTowersAbelian l E T)
    {m n : ℕ} (h : m ≤ n) (s : ScalarCoordinates l E T a h)
    (C : spDerivedCoefficientTowers l E T a) :
    (scalarExtensionFunctor (quotient l E h) T).obj
      ((spDerivedCoefficientEvaluation l E T a n).obj C) ⟶
      (spDerivedCoefficientEvaluation l E T a m).obj C :=
  s.scalar.inv.app ((spDerivedCoefficientEvaluation l E T a n).obj C) ≫
    (a.reduction h).app C

-- These operation interfaces do not use constructor injectivity or SizeOf equations.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Evaluation and scalar coordinate changes for the already recorded tower category.
The ordinary evaluation comparison fixes sections, so its derived comparison is obtained
by exact localization. Source: blueprint, clauses (1) and (3)
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
structure Coordinates (b : SpTowerShriek.Base l E) where
  abelian : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T
  ordinaryEvaluation : ∀ (T : Scheme.{u}) (n : ℕ),
    (b.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T (abelian T).equivalence n
  sections : ∀ (T : Scheme.{u}) (n : ℕ) (M : spCoefficientTowers l E T)
    (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj M)).val.obj U),
    HEq (((ordinaryEvaluation T n).hom.app M).val.app U x) x
  scalar : ∀ (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n),
    ScalarCoordinates l E T (abelian T) h

/-- Canonical reduction unitor in intrinsic coordinates, obtained from the dependency's
normalized tensor unitor. Source: blueprint clause (3)
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def scalarUnit (b : SpTowerShriek.Base l E) (q : Coordinates l E b)
    (T : Scheme.{u}) (n : ℕ) :
    scalarExtensionFunctor (quotient l E (Nat.le_refl n)) T ≅ 𝟭 _ := by
  letI := (q.abelian T).hasDerived
  exact (q.scalar T (Nat.le_refl n)).scalar.symm ≪≫
    (q.abelian T).tensor.derivedUnit (spCoefficientCommRings l E T) n

/-- Canonical reduction associator in intrinsic coordinates. Each coordinate change
preserves the scalar adjunction, so this is the balanced derived tensor associator.
Source: blueprint clause (3) (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def scalarAssoc (b : SpTowerShriek.Base l E) (q : Coordinates l E b)
    (T : Scheme.{u}) {r m n : ℕ} (h : r ≤ m) (v : m ≤ n) :
    scalarExtensionFunctor (quotient l E v) T ⋙
        scalarExtensionFunctor (quotient l E h) T ≅
      scalarExtensionFunctor (quotient l E (h.trans v)) T := by
  letI := (q.abelian T).hasDerived
  exact Functor.isoWhiskerRight (q.scalar T v).scalar.symm _ ≪≫
    Functor.isoWhiskerLeft _ (q.scalar T h).scalar.symm ≪≫
    (q.abelian T).tensor.derivedAssoc (spCoefficientCommRings l E T) h v ≪≫
    (q.scalar T (h.trans v)).scalar

/-- The exact-localization comparison of the preceding ordinary section identity.
Source: blueprint, finite evaluation (blueprint: lem-sp-coefficient-tower-shriek-calculus).
-/
def levelComparison (b : SpTowerShriek.Base l E) (q : Coordinates l E b)
    (T : Scheme.{u}) (n : ℕ) :
    (realization l E b T (q.abelian T)).functor ⋙ SpTowerShriek.Ev l E T n ≅
      spDerivedCoefficientEvaluation l E T (q.abelian T) n := by
  letI := (q.abelian T).hasDerived
  letI := b.realizationAdditive T
  letI := (q.abelian T).equivalenceAdditive
  letI := (q.abelian T).evaluationLimits n
  letI := (q.abelian T).evaluationColimits n
  letI : (spCoefficientEvaluation l E T (q.abelian T).equivalence n).Additive :=
    Functor.additive_of_iso (q.ordinaryEvaluation T n)
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (q.ordinaryEvaluation T n)

/-- The finite sheaf extension along an etale localization is left Kan extension followed
by sheafification, transported by the existing intrinsic module equivalences.
Source: Stacks 03DI, 03S5 (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def finiteEtaleExtension {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleRingModules U (proEtaleConstantRing U A) ⥤
      proEtaleRingModules T (proEtaleConstantRing T A) :=
  (sfIntrinsicModuleEquivalence U A).inverse ⋙
    Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e))
      (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology T) ⋙
    (sfIntrinsicModuleEquivalence T A).functor

-- These operation interfaces do not use constructor injectivity or SizeOf equations.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Identify the canonical direct-image coordinates by the identity on underlying
sections. This fixes every later finite-coordinate change, including adjunction units.
Source: blueprint, ordinary finite operations
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
structure FiniteCoordinates where
  direct : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
    proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f ≅
      proEtaleConstantModuleDirectImage f (SpTowerShriek.R l E n)
  sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : proEtaleRingModules X (proEtaleConstantRing X (SpTowerShriek.R l E n)))
    (U : Y.ProEtᵒᵖ)
    (x : ((proEtaleConstantRingPushforward (SpTowerShriek.R l E n) f).obj M).val.obj U),
    HEq (((direct f n).hom.app M).val.app U x) x

/-- The canonical finite compact-support coordinate change, induced by the ordinary
identity on direct-image sections and hence on K-injective representatives.
Source: blueprint, clause (3) (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def finiteSupportCoordinates (b : SpTowerShriek.Base l E) (z : FiniteCoordinates l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g ≅
      sfIntrinsicCompactSupport c (SpTowerShriek.R l E n) :=
  Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso (z.direct c.g n))

/-- Finite compact support in fixed module coordinates, with its existing normalized
proper comparison. This is an explicit word in realization units and counits.
Source: blueprint, finite composition normalization
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def fixedSupportCoordinates (b : SpTowerShriek.Base l E) (z : FiniteCoordinates l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g ⋙
        (sfIntrinsicDerivedEquivalence Y (SpTowerShriek.R l E n)).inverse ≅
      (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) c :=
  Functor.isoWhiskerRight (finiteSupportCoordinates l E b z c n) _ ≪≫
    CategoryTheory.Iso.isoInverseComp ((Functor.associator _ _ _).symm ≪≫
      (sfIntrinsicCompactSupportComparison (SpTowerShriek.R l E n) c).compInverseIso)

/-- The finite etale adjunction, with the sheafification/Kan-extension unit and the
sum counit. The right-coordinate change is uniquely fixed as a left-adjoint comparison
against the section-normalized direct image, so no choice of adjunction is introduced.
Source: Stacks 03DI, 03S5 (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def finiteEtaleAdjunction (b : SpTowerShriek.Base l E) (z : FiniteCoordinates l E)
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (n : ℕ) :
    finiteEtaleExtension e (SpTowerShriek.R l E n) ⊣
      proEtaleConstantRingPullback (SpTowerShriek.R l E n) e :=
  ((((sfIntrinsicModuleEquivalence U (SpTowerShriek.R l E n)).symm.toAdjunction.comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e))
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology T))).comp
    (sfIntrinsicModuleEquivalence T (SpTowerShriek.R l E n)).toAdjunction).ofNatIsoRight
      (sfIntrinsicTransportIso (SpTowerShriek.R l E n)
        (ProEtale.upperStarIsoLocalizationRestriction
          (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) e
          (inferInstance : WeaklyEtale e)).symm ≪≫
        (sfIntrinsicConstantModuleAdjunction e (SpTowerShriek.R l E n)).leftAdjointUniq
          ((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) e).ofNatIsoRight
            (z.direct e n))))

-- These operation interfaces do not use constructor injectivity or SizeOf equations.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Exact etale sum-extension on strict systems, before derived localization. Its
ordinary finite units and counits fix every comparison. The equations under Q fix the
ordinary unbounded derived adjunction, rather than lifting evaluated derived maps.
Source: Stacks 03DI--03DJ, 03S5; blueprint clause (2)
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
structure EtaleOperation (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (z : FiniteCoordinates l E) {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] where
  extension : SpTowerShriek.S l E U ⥤ SpTowerShriek.S l E T
  [additive : extension.Additive]
  [limits : PreservesFiniteLimits extension]
  [colimits : PreservesFiniteColimits extension]
  ordinaryAdjunction : extension ⊣ (o.geometry e).pull
  [finiteAdditive : ∀ n : ℕ, (finiteEtaleExtension e (SpTowerShriek.R l E n)).Additive]
  [finiteLimits : ∀ n : ℕ,
    PreservesFiniteLimits (finiteEtaleExtension e (SpTowerShriek.R l E n))]
  [finiteColimits : ∀ n : ℕ,
    PreservesFiniteColimits (finiteEtaleExtension e (SpTowerShriek.R l E n))]
  evaluation : ∀ n : ℕ, extension ⋙ SpTowerShriek.ev l E T n ≅
    SpTowerShriek.ev l E U n ⋙ finiteEtaleExtension e (SpTowerShriek.R l E n)
  unit_evaluation : ∀ (n : ℕ) (M : SpTowerShriek.S l E U),
    (SpTowerShriek.ev l E U n).map (ordinaryAdjunction.unit.app M) ≫
      ((o.geometry e).ordinaryPullEvaluation n).hom.app (extension.obj M) ≫
      (proEtaleConstantRingPullback (SpTowerShriek.R l E n) e).map
        ((evaluation n).hom.app M) =
    (finiteEtaleAdjunction l E b z e n).unit.app ((SpTowerShriek.ev l E U n).obj M)
  counit_evaluation : ∀ (n : ℕ) (M : SpTowerShriek.S l E T),
    (evaluation n).inv.app ((o.geometry e).pull.obj M) ≫
      (SpTowerShriek.ev l E T n).map (ordinaryAdjunction.counit.app M) =
    (finiteEtaleExtension e (SpTowerShriek.R l E n)).map
      (((o.geometry e).ordinaryPullEvaluation n).hom.app M) ≫
      (finiteEtaleAdjunction l E b z e n).counit.app ((SpTowerShriek.ev l E T n).obj M)
  derivedAdjunction : extension.mapDerivedCategory ⊣ SpTowerShriek.pull l E b (o.geometry e)
  unit_termwise : derivedAdjunction.unit =
    (Functor.mapDerivedCategoryIdIso _).inv ≫
      SpTowerShriek.deriveMap l E ordinaryAdjunction.unit ≫
      (Functor.mapDerivedCategoryCompIso extension (o.geometry e).pull).inv
  counit_termwise : derivedAdjunction.counit =
    (Functor.mapDerivedCategoryCompIso (o.geometry e).pull extension).hom ≫
      SpTowerShriek.deriveMap l E ordinaryAdjunction.counit ≫
      (Functor.mapDerivedCategoryIdIso _).hom

attribute [instance] EtaleOperation.additive EtaleOperation.limits EtaleOperation.colimits

/-- Canonical compactification comparison on the full finite etale-origin class.
It is the unique preimage of the existing normalized comparison on etale D+.
Source: Stacks 0F7I (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def fixedRefinement (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).asEquivalence.congrLeft
    |>.fullyFaithfulInverse).preimageIso (fixedCompactSupportOriginIso A c d)

/-- The canonical finite composition with arbitrary compactifications, obtained by
conjugating the existing canonical compositor by the canonical refinement maps.
Source: Stacks 0F7J (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def fixedComposition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
      (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (fixedRefinement A c (HasCompactification.compactification f)) _ ≪≫
    Functor.associator (originCompactSupport A f)
      (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).ι _ ≪≫
    Functor.isoWhiskerLeft (originCompactSupport A f)
      (fixedRefinement A d (HasCompactification.compactification g)) ≪≫
    (Functor.associator (originCompactSupport A f)
      (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).ι _).symm ≪≫
    Functor.associator _ _ _ ≪≫
    originCompositionAmbient A f g ≪≫
    (fixedRefinement A e (HasCompactification.compactification (f ≫ g))).symm

/-- The actual full constructible finite-Tor tower category; no normalization is imposed.
Source: blueprint, standing convention (blueprint: lem-sp-coefficient-tower-shriek-calculus).
-/
abbrev C (b : SpTowerShriek.Base l E) (q : Coordinates l E b) (T : Scheme.{u}) :=
  spConstructibleTorTowerCategory l E T (q.abelian T)

/-- Its full inclusion into the original ordinary derived category.
Source: blueprint, standing convention (blueprint: lem-sp-coefficient-tower-shriek-calculus).
-/
abbrev inclusion (b : SpTowerShriek.Base l E) (q : Coordinates l E b) (T : Scheme.{u}) :=
  (spConstructibleTorTowers l E T (q.abelian T)).ι

/-- The recorded compact-support functor in the original tower coordinates.
Source: blueprint, F_h (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
abbrev F (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  compactSupport l E b o q.abelian c

-- These operation interfaces do not use constructor injectivity or SizeOf equations.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Its natural finite evaluation, with the normalization supplied by the already
constructed Fcomparison. Source: blueprint, finite evaluations in clauses (1)--(3)
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
structure Evaluation (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (n : ℕ) where
  comparison : F l E b o q c ⋙ spDerivedCoefficientEvaluation l E Y (q.abelian Y) n ≅
    spDerivedCoefficientEvaluation l E X (q.abelian X) n ⋙
      reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g
  normalization : ∀ M : spDerivedCoefficientTowers l E X (q.abelian X),
    comparison.hom.app M =
      (levelComparison l E b q Y n).inv.app ((F l E b o q c).obj M) ≫
      (SpTowerShriek.Ev l E Y n).map
        ((realization l E b Y (q.abelian Y)).counitIso.hom.app
          ((SpTowerShriek.F l E b o c).obj
            ((realization l E b X (q.abelian X)).functor.obj M))) ≫
      (SpTowerShriek.Fcomparison l E b o c n).hom.app
        ((realization l E b X (q.abelian X)).functor.obj M) ≫
      (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map
        ((levelComparison l E b q X n).hom.app M)

/-- Evaluation in fixed module coordinates, using only the canonical coordinate words.
Source: blueprint, canonical finite normalization
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def fixedEvaluation (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (v : Evaluation l E b o q c n) :
    F l E b o q c ⋙ spDerivedCoefficientEvaluation l E Y (q.abelian Y) n ⋙
        (sfIntrinsicDerivedEquivalence Y (SpTowerShriek.R l E n)).inverse ≅
      spDerivedCoefficientEvaluation l E X (q.abelian X) n ⋙
        (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight v.comparison _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (fixedSupportCoordinates l E b z c n)

/-- A fixed-coordinate finite evaluation of an object of the recorded tower category.
Source: blueprint, finite constructible origins
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
abbrev fixedLevel (b : SpTowerShriek.Base l E) (q : Coordinates l E b)
    (T : Scheme.{u}) (n : ℕ) :=
  spDerivedCoefficientEvaluation l E T (q.abelian T) n ⋙
    (sfIntrinsicDerivedEquivalence T (SpTowerShriek.R l E n)).inverse

/-- Canonical finite composition using the supplied compactifications as existence witnesses.
Source: Stacks 0F7J, 03DI--03DJ, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def finiteCanonicalComposition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  fixedComposition A f g c d e

/-- Etale extension on the original ordinary derived tower category, by exact localization.
Source: Stacks 0F7J, 03DI--03DJ, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def etaleExtension (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    {U T : Scheme.{u}} {e : U ⟶ T} [Etale e] (d : EtaleOperation l E b o z e) :=
  (realization l E b U (q.abelian U)).functor ⋙ d.extension.mapDerivedCategory ⋙
    (realization l E b T (q.abelian T)).inverse

/-- Exact inverse image on the original ordinary derived tower category.
Source: Stacks 0F7J, 03DI--03DJ, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def etalePullback (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) {U T : Scheme.{u}} (e : U ⟶ T) :=
  (realization l E b T (q.abelian T)).functor ⋙
    SpTowerShriek.pull l E b (o.geometry e) ⋙
    (realization l E b U (q.abelian U)).inverse

/-- The etale adjunction on the entire ordinary unbounded derived category, transported through
  the
  real realization equivalences.
Source: Stacks 0F7J, 03DI--03DJ, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def etaleAdjunction (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    {U T : Scheme.{u}} {e : U ⟶ T} [Etale e] (d : EtaleOperation l E b o z e) :
    etaleExtension l E b o q z d ⊣ etalePullback l E b o q e :=
  ((realization l E b U (q.abelian U)).toAdjunction.comp d.derivedAdjunction).comp
    (realization l E b T (q.abelian T)).symm.toAdjunction

/-- Exact finite etale extension, derived termwise on all complexes.
Source: Stacks 0F7J, 03DI--03DJ, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def finiteEtaleDerived (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (z : FiniteCoordinates l E) {U T : Scheme.{u}} {e : U ⟶ T} [Etale e]
    (d : EtaleOperation l E b o z e) (n : ℕ) :=
  letI := d.finiteAdditive n
  letI := d.finiteLimits n
  letI := d.finiteColimits n
  (finiteEtaleExtension e (SpTowerShriek.R l E n)).mapDerivedCategory

/-- Vanishing outside the specified cohomological interval, using the existing ordinary cohomology
  functor.
Source: Stacks 0F7J, 03DI--03DJ, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def cohomologicalInterval (T : Scheme.{u}) (n : ℕ)
    (K : proEtaleDerivedCategory T (SpTowerShriek.R l E n)) (a b : ℤ) : Prop :=
  ∀ i : ℤ, (i < a ∨ b < i) → IsZero
    ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T (SpTowerShriek.R l E n))) i).obj K)

/-- The preservation assumption, exactly at the separated finite-type maps where compact support
  is
  restricted. No tower normalization is required.
Source: Stacks 0F7J, 03DI--03DJ, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def Preservation (k : Type u) [Field k] (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations
  l E b)
    (q : Coordinates l E b) : Prop :=
  ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (K : spDerivedCoefficientTowers l E X (q.abelian X)),
    spConstructibleTorTowers l E X (q.abelian X) K →
      spConstructibleTorTowers l E Y (q.abelian Y) ((F l E b o q c).obj K)

/-- The genuine restriction of compact support to the full ordinary constructible finite-Tor tower
  categories, under the stated preservation assumption.
Source: Stacks 0F7J, 03DI--03DJ, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def restrictedSupport (k : Type u) [Field k] (b : SpTowerShriek.Base l E) (o :
  SpTowerShriek.Operations l E b)
    (q : Coordinates l E b)
    (h : Preservation l E k b o q) {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) : C l E b q
      X
      ⥤ C l E b q Y :=
  ObjectProperty.lift _ (inclusion l E b q X ⋙ F l E b o q c)
    (fun K ↦ h f c K.obj K.property)

/-- Open extension in original tower coordinates, using the recorded extension by zero.
Source: blueprint clause (1) (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def openExtension (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (realization l E b U (q.abelian U)).functor ⋙
    SpTowerShriek.openD l E b (o.openOp j) ⋙
    (realization l E b T (q.abelian T)).inverse

/-- The etale construction is extension by zero for an open immersion, with the
unique comparison preserving the ordinary adjunction and hence its canonical counit.
Source: Stacks 03S5 (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def openEtaleCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    (z : FiniteCoordinates l E) {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (d : EtaleOperation l E b o z j) :
    etaleExtension l E b o q z d ≅ openExtension l E b o q j :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (d.ordinaryAdjunction.leftAdjointUniq (o.openOp j).ordinaryAdjunction)) _)

/-- Composition of transported functors, with the canonical realization counit.
Source: blueprint, ordinary section-model transport
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def composeTransport (b : SpTowerShriek.Base l E) (q : Coordinates l E b)
    {X Y Z : Scheme.{u}} (f : SpTowerShriek.D l E X ⥤ SpTowerShriek.D l E Y)
    (g : SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E Z) :
    ((realization l E b X (q.abelian X)).functor ⋙ f ⋙
        (realization l E b Y (q.abelian Y)).inverse) ⋙
      ((realization l E b Y (q.abelian Y)).functor ⋙ g ⋙
        (realization l E b Z (q.abelian Z)).inverse) ≅
      (realization l E b X (q.abelian X)).functor ⋙ (f ⋙ g) ⋙
        (realization l E b Z (q.abelian Z)).inverse :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft f
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (realization l E b Y (q.abelian Y)).counitIso _ ≪≫
        Functor.leftUnitor _)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm

/-- The canonical composition of open extensions is the unique left-adjoint
comparison to composition of exact inverse images; this fixes the open counits.
Source: Stacks 0F7J (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def sequenceOpenComposition (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {U X Y : Scheme.{u}}
    (j : U ⟶ X) (i : X ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion i] :
    SpTowerShriek.openD l E b (o.openOp j) ⋙
      SpTowerShriek.openD l E b (o.openOp i) ≅
      SpTowerShriek.openD l E b (o.openOp (j ≫ i)) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      ((((o.openOp j).ordinaryAdjunction.comp (o.openOp i).ordinaryAdjunction).ofNatIsoRight
        (o.ordinaryComp j i)).leftAdjointUniq (o.openOp (j ≫ i)).ordinaryAdjunction)

/-- Canonical open normalization F_h u_! = F_(hu). The word uses the normalized
ordinary open composition and realization counits, before any finite evaluation.
Source: Stacks 0F7J (blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
def openComposition (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {f : X ⟶ Y} (c : Compactification f) :
    openExtension l E b o q j ⋙ F l E b o q c ≅ F l E b o q (c.precomp j) :=
  composeTransport l E b q _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (sequenceOpenComposition l E b o j c.i) _) _)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- FiniteNormalization for the ordinary strict tower calculus.
Source: Stacks 0F7J, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
structure FiniteNormalization (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    (z : FiniteCoordinates l E) where
  evaluation : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ),
    Evaluation l E b o q c n
  finite_origin : ∀ {T : Scheme.{u}}
    [T.Over (Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (K : C l E b q T) (n : ℕ),
    ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) T
        ((fixedLevel l E b q T n).obj K.obj)

-- These operation interfaces do not use constructor injectivity or SizeOf equations.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- CompositionOperations for the ordinary strict tower calculus.
Source: Stacks 0F7J, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
structure CompositionOperations (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    (z : FiniteCoordinates l E) where
  identity : ∀ {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (c : Compactification (𝟙 X)),
    inclusion l E b q X ⋙ F l E b o q c ≅ inclusion l E b q X
  refinement : ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f),
    inclusion l E b q X ⋙ F l E b o q c ≅ inclusion l E b q X ⋙ F l E b o q d
  composition : ∀ {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [Z.Over (Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (fg : X ⟶ Z) (_w : f ≫ g = fg)
    (c : Compactification f) (d : Compactification g) (e : Compactification fg),
    inclusion l E b q X ⋙ F l E b o q c ⋙ F l E b o q d ≅
      inclusion l E b q X ⋙ F l E b o q e

-- These operation interfaces do not use constructor injectivity or SizeOf equations.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- CompositionCoherence for the ordinary strict tower calculus.
Source: Stacks 0F7J, 03S5; blueprint Local pairs and Levels
(blueprint: lem-sp-coefficient-tower-shriek-calculus). -/
structure CompositionCoherence (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    (z : FiniteCoordinates l E)
    (h : Preservation l E k b o q) (finiteData : FiniteNormalization l E k b o q z)
    (opsData : CompositionOperations l E k b o q z) where
  refinement_identity : ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f), opsData.refinement f c c = Iso.refl _
  refinement_transitive : ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d e : Compactification f),
    opsData.refinement f c d ≪≫ opsData.refinement f d e = opsData.refinement f c e
  refinement_finite : ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (K : C l E b q X) (n : ℕ),
    (fixedLevel l E b q Y n).map ((opsData.refinement f c d).hom.app K) ≫
      (fixedEvaluation l E b o q z d n (finiteData.evaluation d n)).hom.app K.obj =
    (fixedEvaluation l E b o q z c n (finiteData.evaluation c n)).hom.app K.obj ≫
      (fixedRefinement (ULift.{u + 1} (SpTowerShriek.R l E n)) c d).hom.app
        ⟨(fixedLevel l E b q X n).obj K.obj, finiteData.finite_origin K n⟩
  composition_finite : ∀ {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [Z.Over (Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (c : Compactification f) (d :
      Compactification g)
    (e : Compactification (f ≫ g)) (K : C l E b q X) (n : ℕ),
    (fixedLevel l E b q Z n).map ((opsData.composition f g (f ≫ g) rfl c d e).hom.app K) ≫
      (fixedEvaluation l E b o q z e n (finiteData.evaluation e n)).hom.app K.obj =
    (fixedEvaluation l E b o q z d n (finiteData.evaluation d n)).hom.app ((F l E b o q c).obj
      K.obj) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) d).map
        ((fixedEvaluation l E b o q z c n (finiteData.evaluation c n)).hom.app K.obj) ≫
      (finiteCanonicalComposition (ULift.{u + 1} (SpTowerShriek.R l E n)) f g c d e).hom.app
        ⟨(fixedLevel l E b q X n).obj K.obj, finiteData.finite_origin K n⟩
  identity_left : ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (i : Compactification (𝟙 X)) (K : C l E b q X),
    (opsData.composition (𝟙 X) f f (Category.id_comp f) i c c).hom.app K =
      (F l E b o q c).map ((opsData.identity i).hom.app K)
  identity_right : ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (i : Compactification (𝟙 Y)) (K : C l E b q X),
    (opsData.composition f (𝟙 Y) f (Category.comp_id f) c i c).hom.app K =
      (opsData.identity i).hom.app ((restrictedSupport l E k b o q h f c).obj K)
  associativity : ∀ {X Y Z W : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [Z.Over (Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [W.Over (Spec (.of k))] [IsSeparated (W ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] (t : Z ⟶ W) [t.IsOver (Spec (.of k))]
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    (c : Compactification f) (d : Compactification g) (e : Compactification t)
    (cd : Compactification (f ≫ g)) (de : Compactification (g ≫ t))
    (cde : Compactification ((f ≫ g) ≫ t)) (K : C l E b q X),
    (F l E b o q e).map ((opsData.composition f g (f ≫ g) rfl c d cd).hom.app K) ≫
      (opsData.composition (f ≫ g) t ((f ≫ g) ≫ t) rfl cd e cde).hom.app K =
    (opsData.composition g t (g ≫ t) rfl d e de).hom.app
        ((restrictedSupport l E k b o q h f c).obj K) ≫
      (opsData.composition f (g ≫ t) ((f ≫ g) ≫ t) (Category.assoc f g t).symm c de cde).hom.app K
  refinement_composition : ∀ {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [Z.Over (Spec (.of k))] [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c c' : Compactification f) (d d' : Compactification g)
    (e e' : Compactification (f ≫ g)) (K : C l E b q X),
    (F l E b o q d).map ((opsData.refinement f c c').hom.app K) ≫
      (opsData.refinement g d d').hom.app ((restrictedSupport l E k b o q h f c').obj K) ≫
      (opsData.composition f g (f ≫ g) rfl c' d' e').hom.app K =
    (opsData.composition f g (f ≫ g) rfl c d e).hom.app K ≫ (opsData.refinement (f ≫ g) e
      e').hom.app K
  triangulated : ∀ {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f), ∃ (_ : (F l E b o q c).CommShift ℤ),
      (F l E b o q c).IsTriangulated

end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
