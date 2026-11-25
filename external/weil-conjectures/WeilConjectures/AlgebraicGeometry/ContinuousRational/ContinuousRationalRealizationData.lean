/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.AlgebraicGeometry.Localized.LocalizedTStructure
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarStandardCohomology
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Continuous rational derived realization data

Source: Bhatt--Scholze, Proposition 6.8.14(2), Lemma 6.8.2(1), Proposition 6.8.11(3),
Definition 6.8.8 and Remark 6.8.15
(blueprint: lem-per-continuous-rational-derived-realization).

## Main definitions and statement

* `ContinuousRational.At`: normalized equivalence at one scheme.
* `ContinuousRational.Along`: canonical derived module pullback comparison.
* `ContinuousRational.Family`: coherent scheme and coefficient comparisons.
The existence theorem is in `ContinuousRationalDerivedRealization`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.ContinuousRational

/-- The geometric hypotheses of BS 6.8.14, including the empty scheme.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure Base (l : ℕ) where
  scheme : Scheme.{u}
  [noetherian : IsNoetherian scheme]
  dimension : ∃ n : ℕ, topologicalKrullDim scheme ≤ n
  prime_unit : ∀ x : scheme, IsUnit (l : scheme.presheaf.stalk x)

attribute [instance] Base.noetherian

/-- The recorded dimension bound as a typeclass argument.
Source: BS 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
instance baseDimension {l : ℕ} (X : Base.{u} l) :
    Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) := ⟨X.dimension⟩

/-- The recorded scheme-level invertibility hypothesis.
Source: BS 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
instance basePrimeUnit {l : ℕ} (X : Base.{u} l) :
    Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x)) := ⟨X.prime_unit⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Constant continuous functions supply the field action on rational modules.
Source: BS 6.8.1 (blueprint: lem-per-continuous-rational-derived-realization). -/
def scalarSections (X : Scheme.{u}) :
    E →+* RingCat.sectionsSubring
      ((rationalCoefficientSheaf l X E).obj ⋙ forget₂ CommRingCat RingCat) := by
  letI := coefficientExtensionNormedField l E
  exact
    { toFun := fun a ↦ ⟨fun _ ↦ ContinuousMap.const _ (ULift.up a), fun _ ↦ rfl⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The field action induced by those constant sections.
Source: BS 6.8.1 (blueprint: lem-per-continuous-rational-derived-realization). -/
instance moduleLinear (X : Scheme.{u}) :
    Linear E (pbcModules X (rationalCoefficientSheaf l X E)) :=
  letI : Linear (RingCat.sectionsSubring
      ((rationalCoefficientSheaf l X E).obj ⋙ forget₂ CommRingCat RingCat))
      (pbcModules X (rationalCoefficientSheaf l X E)) :=
    SheafOfModules.homLinear (rationalCoefficientSheaf l X E).obj
      (((adicLisseForget X).obj (rationalCoefficientSheaf l X E)).property)
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (scalarSections l E X)
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (scalarSections l E X a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (scalarSections l E X a) g }

/-- The inherited field action on the ambient derived category.
Source: BS 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
instance derivedLinear (X : Scheme.{u}) :
    Linear E (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
  inferInstance

/-- Reuse the recorded constructible continuous-module predicate via its coefficient
encoding. Over the field E its finitely presented local models are exactly finite free models.
Source: BS 6.8.6 and 6.8.10
(blueprint: lem-per-continuous-rational-derived-realization). -/
abbrev IsConstructible (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (e : AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅ rationalCoefficientSheaf l X E)
    (F : pbcModules X (rationalCoefficientSheaf l X E)) : Prop :=
  AlgebraicGeometry.ProEtale.IsContinuousConstructible X
    (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ((pbcRestrict e.hom).obj F)

/-- The full ambient bounded constructible subcategory, using the recorded sheaf predicate.
Source: BS 6.8.8 (blueprint: lem-per-continuous-rational-derived-realization). -/
def IsDerivedConstructible (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (e : AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅ rationalCoefficientSheaf l X E) :
    ObjectProperty (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
  fun K ↦ (∃ a b : ℤ, K.IsGE a ∧ K.IsLE b) ∧
    ∀ r : ℤ, IsConstructible l E X e ((DerivedCategory.homologyFunctor _ r).obj K)

/-- The localized standard t-structure supplied by the recorded dependency.
Its two classes are uniquely specified as the strictly full images of integral bounds.
Source: BS 6.8.11 and 6.8.14
(blueprint: lem-per-continuous-rational-derived-realization). -/
def localizedT (X : Base.{u} l) :=
  (pbc_localized_tstructure X.scheme l E).choose

/-- Cohomology placed in degree zero, using the actual localized truncations and shift.
Source: BS 6.8.11 (blueprint: lem-per-continuous-rational-derived-realization). -/
def localizedCohomology (X : Base.{u} l) (r : ℤ) :=
  (localizedT l E X).truncLE r ⋙ (localizedT l E X).truncGE r ⋙
    shiftFunctor (PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) r

/-- A normalized realization at one scheme. Bijectivity on Homs and the exact essential-image
condition express an equivalence onto the full ambient subcategory. The natural integral
comparison and fraction equation fix this functor on representatives and all arrows.
Source: BS 6.8.2, 6.8.11, 6.8.14 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure At (X : Base.{u} l) where
  [topNoetherian : TopologicalSpace.NoetherianSpace X.scheme]
  encoding : AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X.scheme
    (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
      rationalCoefficientSheaf l X.scheme E
  encoding_normalization : ∀ (U : X.scheme.ProEtᵒᵖ)
      (f : C(U.unop.left, WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
      (x : U.unop.left),
    rationalCoefficientValue l E X.scheme U (encoding.hom.hom.app U (ULift.up f)) x =
      WithAbs.ofAbs (f x)
  strata_criterion : ∀ F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E),
    IsConstructible l E X.scheme encoding F ↔
      ∃ s : FiniteLocallyClosedStratification X.scheme, ∀ i : Fin s.n,
        ((proEtaleModuleInverseImage (s.immersion i)
          (rationalCoefficientSheaf l X.scheme E)).obj F).IsFiniteLocallyFree
  integralIso : pbcAdicCompletion X.scheme (pbcIntegralDatum l E) ≅
    integralCoefficientSheaf l X.scheme E
  finiteIso : ∀ n : ℕ,
    (pbcAdicRings X.scheme (pbcIntegralDatum l E)).obj (op n) ≅
      finiteContinuousCoefficientSheaf l X.scheme E n
  finite_normalization : ∀ (n : ℕ) (U : X.scheme.ProEtᵒᵖ)
      (a : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1)) (x : U.unop.left),
    finiteContinuousCoefficientValue l E X.scheme n U
      ((finiteIso n).hom.hom.app U
        (pbcFunctionScalars X.scheme (pbcIntegralDatum l E) n |>.app U |>.hom <| a)) x =
      integralCoefficientULift l E n a
  integral_normalization : ∀ (n : ℕ) (U : X.scheme.ProEtᵒᵖ)
      (s : (integralCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E X.scheme n U
      ((integralIso.inv ≫ pbcAdicProjection X.scheme (pbcIntegralDatum l E) n ≫
        (finiteIso n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E X.scheme U s x)
  localizationIso : integralCoefficientLocalization l X.scheme E ≅
    rationalCoefficientSheaf l X.scheme E
  localization_normalization :
    integralCoefficientLocalizationNormalized l E X.scheme localizationIso.hom
  inclusion : integralCoefficientSheaf l X.scheme E ⟶ rationalCoefficientSheaf l X.scheme E
  inclusion_normalization : integralRationalCoefficientNormalized l E X.scheme inclusion
  J : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
    DerivedCategory (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
  [additive : J.Additive]
  [linear : J.Linear E]
  [shift : J.CommShift ℤ]
  triangulated : J.IsTriangulated
  fully_faithful : ∀ K L, Function.Bijective (J.map : (K ⟶ L) → (J.obj K ⟶ J.obj L))
  image : ∀ C, IsDerivedConstructible l E X.scheme encoding C ↔ ∃ K, Nonempty (J.obj K ≅ C)
  integral : pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙ J ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) ⋙
      pbcDerivedExtend (integralIso.hom ≫ inclusion)
  fractions : ∀ (K L : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))
      (f : K ⟶ L) (a : Localization.Away (pbcUniformizer l E)),
    J.map (a •
      (pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) =
      pbcRationalCoefficientEquiv l E a •
        J.map ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map f)
  t_bounds : ∀ K (r : ℤ),
    ((localizedT l E X).le r K ↔ (J.obj K).IsLE r) ∧
      ((localizedT l E X).ge r K ↔ (J.obj K).IsGE r)
  heart : ∀ K, (localizedT l E X).heart K ↔
    ∃ F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E),
      IsConstructible l E X.scheme encoding F ∧
        Nonempty (J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F)
  cohomology : ∀ r : ℤ,
    pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        localizedCohomology l E X r ⋙ J ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) ⋙
        DerivedCategory.homologyFunctor _ r ⋙ pbcExtend (integralIso.hom ≫ inclusion) ⋙
          DerivedCategory.singleFunctor _ 0

attribute [instance] At.additive At.linear At.shift

/-- Ordinary ringed module inverse image for an arbitrary coefficient structure map.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
def modulePull {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage g).obj R ⟶ S) :=
  proEtaleModuleInverseImage g R ⋙ pbcExtend c

attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModelUp_isContinuous in
/-- The actual tensor unit over a base-changed site object, for arbitrary coefficients.
Source: BS 6.8.15; Stacks 03EL
(blueprint: lem-per-continuous-rational-derived-realization). -/
def moduleUnit {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage g).obj R ⟶ S)
    (M : pbcModules Y R) (U : Y.ProEt) (m : M.val.obj (op U)) :
    ((modulePull g c).obj M).val.obj (op ((proEtaleBaseChange g).obj U)) :=
  pbcTensorSection c ((proEtaleModuleInverseImage g R).obj M)
    (op ((proEtaleBaseChange g).obj U)) 1
    (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1} (proEtaleModelRingUnit g R)).unit.app
      ((proEtaleModuleToModel ((adicLisseForget Y).obj R)).obj M)).val.app
        (op (AsSmall.up.obj U)) m)

/-- Actual derived module inverse image: exact ring inverse image followed by derived tensor.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
def derivedPull {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage g).obj R ⟶ S) :=
  adicTowerPullback g R ⋙ pbcDerivedExtend c

/-- The canonical counit for derived module inverse image. The exact inverse-image
API inserts scalar extension along the identity ring map. The first two comparisons
remove precisely that identity tensor factor. Their section equation is multiplication,
and the final equation fixes the derived counit on every complex.
Source: BS 6.8.15; Stacks 03EL, 03EK
(blueprint: lem-per-continuous-rational-derived-realization). -/
def IsNormalizedPullCounit {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage g).obj R ⟶ S) [(modulePull g c).Additive]
    (δ : DerivedCategory.Q ⋙ derivedPull g c ⟶
      (modulePull g c).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) : Prop :=
  ∃ (e : proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _) ⋙
        pbcExtend c ≅ modulePull g c)
    (eC : (proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R)
        (Iso.refl _)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcExtend c).mapHomologicalComplex (.up ℤ) ≅
      (modulePull g c).mapHomologicalComplex (.up ℤ)),
    (∀ P (n : ℤ), (eC.hom.app P).f n = e.hom.app (P.X n)) ∧
    (∀ (M : pbcModules Y R) (W : X.ProEtᵒᵖ) (s : S.obj.obj W)
        (m : ((proEtaleModuleInverseImage g R).obj M).val.obj W),
      (e.hom.app M).val.app W
        (pbcTensorSection c
          ((proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R)
            (Iso.refl _)).obj M) W s
          ((eqToHom ((completedAdicChangeData
            X (𝟙 ((adicTowerInverseImage g).obj R))).choose_spec.choose
              ((proEtaleModuleInverseImage g R).obj M))).val.app W
              (pbcTensorSection (𝟙 ((adicTowerInverseImage g).obj R))
                ((proEtaleModuleInverseImage g R).obj M) W 1 m))) =
        pbcTensorSection c ((proEtaleModuleInverseImage g R).obj M) W s m) ∧
    ∀ P, δ.app P =
      (pbcDerivedExtend c).map
          ((proEtaleRingDerivedPullbackFactors g R ((adicTowerInverseImage g).obj R)
            (Iso.refl _)).hom.app P) ≫
        pbcComplexCounit c
          (((proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R)
            (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (eC.hom.app P)

/-- The literal restriction of actual completed pullback, with its preservation certificate.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
abbrev integralPull {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (h : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj)) :=
  pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualCompletedPull g (pbcIntegralDatum l E)) h

/-- Raw rational pullback is tensor extension on the existing Hom modules.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
abbrev rawPull {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (h : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
      PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj)) :=
  pbcConditionalRational (pbcIntegralDatum l E)
    (pbcActualCompletedPull g (pbcIntegralDatum l E)) h (pbcUniformizer l E)

/-- Pullback comparison, normalized before completion by the ordinary balanced tensor map.
The coefficient map has its continuous-function adjunct. Its square with the integral
coefficient structure map ensures that it is also induced by all finite quotient maps.
Source: BS 6.8.2 and 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure Along {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aX : At l E X) (aY : At l E Y) where
  coefficient : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l Y.scheme E) ⟶
    rationalCoefficientSheaf l X.scheme E
  normalized : rationalCoefficientRestrictionNormalized l E g coefficient
  square : (adicTowerInverseImage g).map (aY.integralIso.hom ≫ aY.inclusion) ≫ coefficient =
    completedCoefficientMap g (pbcIntegralDatum l E) ≫ aX.integralIso.hom ≫ aX.inclusion
  [ordinaryAdditive : (modulePull g coefficient).Additive]
  counit : DerivedCategory.Q ⋙ derivedPull g coefficient ⟶
    (modulePull g coefficient).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  normalized_counit : IsNormalizedPullCounit g coefficient counit
  universal : (derivedPull g coefficient).IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso _ (.up ℤ))
  computes : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E)
      P → IsIso (counit.app P)
  balance : pbcExtend (aY.integralIso.hom ≫ aY.inclusion) ⋙ modulePull g coefficient ≅
    pbcActualModulePull g (pbcIntegralDatum l E) ⋙
      pbcExtend (aX.integralIso.hom ≫ aX.inclusion)
  balance_sections : ∀ (M : pbcModules Y.scheme (pbcAdicCompletion Y.scheme
      (pbcIntegralDatum l E))) (U : Y.scheme.ProEt)
      (a : (rationalCoefficientSheaf l Y.scheme E).obj.obj (op U)) (m : M.val.obj (op U)),
    (balance.hom.app M).val.app (op ((proEtaleBaseChange g).obj U))
      (moduleUnit g coefficient ((pbcExtend (aY.integralIso.hom ≫ aY.inclusion)).obj M) U
        (pbcTensorSection (aY.integralIso.hom ≫ aY.inclusion) M (op U) a m)) =
      pbcTensorSection (aX.integralIso.hom ≫ aX.inclusion)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj U))
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _ coefficient).hom.app
          (op U) a) (pbcActualModuleUnitSection g (pbcIntegralDatum l E) M U m)
  ambient : pbcDerivedExtend (aY.integralIso.hom ≫ aY.inclusion) ⋙
      derivedPull g coefficient ≅
    pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
      pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)
  balanceComplex :
    (pbcExtend (aY.integralIso.hom ≫ aY.inclusion)).mapHomologicalComplex (.up ℤ) ⋙
        (modulePull g coefficient).mapHomologicalComplex (.up ℤ) ≅
      (pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcExtend (aX.integralIso.hom ≫ aX.inclusion)).mapHomologicalComplex (.up ℤ)
  balanceComplex_components : ∀ P (n : ℤ),
    (balanceComplex.hom.app P).f n = balance.hom.app (P.X n)
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (pbcAdicCompletion Y.scheme (pbcIntegralDatum l E))) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := pbcAdicCompletion Y.scheme (pbcIntegralDatum l E)) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y.scheme)
      (R := pbcAdicCompletion Y.scheme (pbcIntegralDatum l E)) (P.X n)) →
    (derivedPull g coefficient).map
        (pbcComplexCounit (aY.integralIso.hom ≫ aY.inclusion) P) ≫
        counit.app (((pbcExtend (aY.integralIso.hom ≫ aY.inclusion)).mapHomologicalComplex
          (.up ℤ)).obj P) ≫ DerivedCategory.Q.map (balanceComplex.hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)).map
          (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
        pbcComplexCounit (aX.integralIso.hom ≫ aX.inclusion)
          (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex
            (.up ℤ)).obj P)
  integral_mem : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)
      ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K.obj)
  comparison : rawPull l E g integral_mem ⋙ aX.J ≅ aY.J ⋙ derivedPull g coefficient
  completion_unit : ∀ K : PbcBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E),
    (ambient.hom.app K.obj) ≫
        (pbcDerivedExtend (aX.integralIso.hom ≫ aX.inclusion)).map
          ((pbcActualCompletedPullUnit g (pbcIntegralDatum l E)).app K.obj) ≫
        (aX.integral.inv.app ((integralPull l E g integral_mem).obj K)) =
      (derivedPull g coefficient).map (aY.integral.inv.app K) ≫
        (comparison.inv.app
          ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K))
  special : Etale g ∨ IsImmersion g →
    IsIso coefficient ∧ PreservesFiniteLimits (modulePull g coefficient) ∧
      PreservesFiniteColimits (modulePull g coefficient)

attribute [instance] Along.ordinaryAdditive

/-- The published raw pullback with its preservation certificate.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
def Along.raw {X Y : Base.{u} l} {g : X.scheme ⟶ Y.scheme}
    {aX : At l E X} {aY : At l E Y} (a : Along l E g aX aY) :=
  rawPull l E g a.integral_mem

/-- Canonical ambient composition, fixed by the insertion of tensor units and the
universal derived counits. The last equation states compatibility of J with precisely
this ambient comparison, rather than a new choice of triangulated composition.
Source: BS 6.8.15; Stacks 0D6D
(blueprint: lem-per-continuous-rational-derived-realization). -/
structure Composition {X Y Z : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (h : Z.scheme ⟶ X.scheme) (aX : At l E X) (aY : At l E Y) (aZ : At l E Z)
    (ag : Along l E g aX aY) (ah : Along l E h aZ aX)
    (ahg : Along l E (h ≫ g) aZ aY) where
  coefficient : ahg.coefficient =
    (proEtaleRingInverseImageComp h g).hom.app (rationalCoefficientSheaf l Y.scheme E) ≫
      (adicTowerInverseImage h).map ag.coefficient ≫ ah.coefficient
  ordinary : modulePull (h ≫ g) ahg.coefficient ≅
    modulePull g ag.coefficient ⋙ modulePull h ah.coefficient
  ordinary_units : ∀ (M : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E))
      (U : Y.scheme.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (h ≫ g)).obj U))
        (moduleUnit (h ≫ g) ahg.coefficient M U m) =
      (((modulePull h ah.coefficient).obj ((modulePull g ag.coefficient).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp h g).hom.app U).op)
          (moduleUnit h ah.coefficient ((modulePull g ag.coefficient).obj M)
            ((proEtaleBaseChange g).obj U) (moduleUnit g ag.coefficient M U m))
  complex : (modulePull (h ≫ g) ahg.coefficient).mapHomologicalComplex (.up ℤ) ≅
    (modulePull g ag.coefficient).mapHomologicalComplex (.up ℤ) ⋙
      (modulePull h ah.coefficient).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  ambient : derivedPull (h ≫ g) ahg.coefficient ≅
    derivedPull g ag.coefficient ⋙ derivedPull h ah.coefficient
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) (P.X n)) →
    ahg.counit.app P ≫ DerivedCategory.Q.map (complex.hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (derivedPull h ah.coefficient).map (ag.counit.app P) ≫
        ah.counit.app (((modulePull g ag.coefficient).mapHomologicalComplex (.up ℤ)).obj P)
  raw : ahg.raw l E ≅
    ag.raw l E ⋙ ah.raw l E
  compatibility : ∀ K,
    ahg.comparison.hom.app K ≫
        ambient.hom.app (aY.J.obj K) =
      aZ.J.map (raw.hom.app K) ≫
        ah.comparison.hom.app ((ag.raw l E).obj K) ≫
        (derivedPull h ah.coefficient).map (ag.comparison.hom.app K)

/-- Identity pullback comparison, normalized by the identity fibre product and tensor unit.
Source: BS 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure Identity (X : Base.{u} l) (a : At l E X)
    (ai : Along l E (𝟙 X.scheme) a a) where
  site : proEtaleBaseChange (𝟙 X.scheme) ≅ 𝟭 X.scheme.ProEt
  site_normalization : ∀ U,
    (site.hom.app U).left = pullback.fst U.hom (𝟙 X.scheme)
  ordinary : modulePull (𝟙 X.scheme) ai.coefficient ≅ 𝟭 _
  ordinary_units : ∀ (M : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
      (U : X.scheme.ProEt) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange (𝟙 X.scheme)).obj U))
        (moduleUnit (𝟙 X.scheme) ai.coefficient M U m) =
      M.val.map (site.hom.app U).op m
  ambient : derivedPull (𝟙 X.scheme) ai.coefficient ≅ 𝟭 _
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X.scheme)
      (R := rationalCoefficientSheaf l X.scheme E) P →
    ai.counit.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P)
  raw : ai.raw l E ≅ 𝟭 _
  compatibility : ∀ K,
    ai.comparison.hom.app K ≫ ambient.hom.app (a.J.obj K) = a.J.map (raw.hom.app K)

variable (F G : Type u) [Field F] [Field G] [Algebra ℚ_[l] F] [Algebra ℚ_[l] G]
  [FiniteDimensional ℚ_[l] F] [FiniteDimensional ℚ_[l] G]

/-- Finite coefficient extension, with its sectionwise field map, finite-integral square,
and comparison normalized by the existing derived balancing maps on integral models.
Source: BS 6.8.14 and 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure FieldChange (i : E →ₐ[ℚ_[l]] F) (X : Base.{u} l)
    (aE : At l E X) (aF : At l F X) where
  coefficient : rationalCoefficientSheaf l X.scheme E ⟶ rationalCoefficientSheaf l X.scheme F
  normalized : ∀ (U : X.scheme.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l X.scheme E).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l F X.scheme U (coefficient.hom.app U s) x =
      i (rationalCoefficientValue l E X.scheme U s x)
  square : pbcScalarCoefficientMap l E F i X.scheme ≫ aF.integralIso.hom ≫ aF.inclusion =
    aE.integralIso.hom ≫ aE.inclusion ≫ coefficient
  comparison : pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit ⋙ aF.J ≅
    aE.J ⋙ pbcDerivedExtend coefficient
  integral_normalization : ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E),
    comparison.hom.app
        ((pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
        (pbcDerivedExtend coefficient).map (aE.integral.hom.app K) ≫
        (pbcReductionNormalization (aE.integralIso.hom ≫ aE.inclusion) coefficient
          (aE.integralIso.hom ≫ aE.inclusion ≫ coefficient) rfl K.obj).hom =
      aF.integral.hom.app
          ((pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj K) ≫
        (pbcReductionNormalization (pbcScalarCoefficientMap l E F i X.scheme)
          (aF.integralIso.hom ≫ aF.inclusion)
          (aE.integralIso.hom ≫ aE.inclusion ≫ coefficient) square K.obj).hom

/-- The coefficient associator is the prescribed raw associator and the ambient balanced
tensor associator. This includes repeated fields and identity field embeddings.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure FieldComposition (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G) (X : Base.{u} l)
    (aE : At l E X) (aF : At l F X) (aG : At l G X)
    (bEF : FieldChange l E F i X aE aF) (bFG : FieldChange l F G j X aF aG)
    (bEG : FieldChange l E G (j.comp i) X aE aG) where
  coefficient : bEF.coefficient ≫ bFG.coefficient = bEG.coefficient
  compatibility : ∀ K,
    aG.J.map (pbcRationalScalarCompComponent l E F G i j X.scheme
        X.dimension X.prime_unit K).hom ≫ bEG.comparison.hom.app K =
      bFG.comparison.hom.app
          ((pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit).obj K) ≫
        (pbcDerivedExtend bFG.coefficient).map (bEF.comparison.hom.app K) ≫
        (pbcReductionNormalization bEF.coefficient bFG.coefficient bEG.coefficient
          coefficient (aE.J.obj K)).hom

/-- The mixed coefficient/pullback square, using the actual raw scalar/completed-pull
comparison and the ordinary balanced tensor map. Source: BS 6.8.14--6.8.15
(blueprint: lem-per-continuous-rational-derived-realization). -/
structure Mixed (i : E →ₐ[ℚ_[l]] F) {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aXE : At l E X) (aYE : At l E Y) (aXF : At l F X) (aYF : At l F Y)
    (agE : Along l E g aXE aYE) (agF : Along l F g aXF aYF)
    (bX : FieldChange l E F i X aXE aXF) (bY : FieldChange l E F i Y aYE aYF) where
  coefficient : (adicTowerInverseImage g).map bY.coefficient ≫ agF.coefficient =
    agE.coefficient ≫ bX.coefficient
  ordinary : pbcExtend bY.coefficient ⋙ modulePull g agF.coefficient ≅
    modulePull g agE.coefficient ⋙ pbcExtend bX.coefficient
  ordinary_sections : ∀ (M : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E))
      (U : Y.scheme.ProEt)
      (a : (rationalCoefficientSheaf l Y.scheme F).obj.obj (op U)) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj U))
      (moduleUnit g agF.coefficient ((pbcExtend bY.coefficient).obj M) U
        (pbcTensorSection bY.coefficient M (op U) a m)) =
      pbcTensorSection bX.coefficient ((modulePull g agE.coefficient).obj M)
        (op ((proEtaleBaseChange g).obj U))
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
          agF.coefficient).hom.app (op U) a)
        (moduleUnit g agE.coefficient M U m)
  complex : (pbcExtend bY.coefficient).mapHomologicalComplex (.up ℤ) ⋙
      (modulePull g agF.coefficient).mapHomologicalComplex (.up ℤ) ≅
    (modulePull g agE.coefficient).mapHomologicalComplex (.up ℤ) ⋙
      (pbcExtend bX.coefficient).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  ambient : pbcDerivedExtend bY.coefficient ⋙ derivedPull g agF.coefficient ≅
    derivedPull g agE.coefficient ⋙ pbcDerivedExtend bX.coefficient
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) (P.X n)) →
    (derivedPull g agF.coefficient).map (pbcComplexCounit bY.coefficient P) ≫
        agF.counit.app (((pbcExtend bY.coefficient).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (complex.hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend bX.coefficient).map (agE.counit.app P) ≫
        pbcComplexCounit bX.coefficient
          (((modulePull g agE.coefficient).mapHomologicalComplex (.up ℤ)).obj P)
  raw : pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit ⋙
      agF.raw l F ≅ agE.raw l E ⋙
        pbcRationalScalarExtension l E F i X.scheme X.dimension X.prime_unit
  raw_normalization : ∀ K,
    HEq (raw.hom.app K)
      ((pbcRationalization X.scheme (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        (ObjectProperty.homMk
          (X := (integralPull l F g agF.integral_mem).obj
            ((pbcEmbeddingIntegralTensor l E F i Y.scheme Y.dimension Y.prime_unit).obj K.obj))
          (Y := (pbcEmbeddingIntegralTensor l E F i X.scheme X.dimension X.prime_unit).obj
            ((integralPull l E g agE.integral_mem).obj K.obj))
          ((pbcScalarCompletedPullIso l E F i g).hom.app K.obj.obj)))
  compatibility : ∀ K,
    aXF.J.map (raw.hom.app K) ≫
        bX.comparison.hom.app ((agE.raw l E).obj K) ≫
        (pbcDerivedExtend bX.coefficient).map (agE.comparison.hom.app K) =
      agF.comparison.hom.app
          ((pbcRationalScalarExtension l E F i Y.scheme Y.dimension Y.prime_unit).obj K) ≫
        (derivedPull g agF.coefficient).map (bY.comparison.hom.app K) ≫
        ambient.hom.app (aYE.J.obj K)

/-- The site inclusion attached to a weakly étale object, with no finiteness hypothesis
on its source. Source: BS 6.8.14; Stacks 03EL
(blueprint: lem-per-continuous-rational-derived-realization). -/
def siteInclude {X : Scheme.{u}} (U : X.ProEt) : U.left.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ U.prop

/-- Projection from the base-changed object, viewed in the original small site.
Source: BS 6.8.15; Stacks 03EL
(blueprint: lem-per-continuous-rational-derived-realization). -/
def siteCounit {X : Scheme.{u}} (U : X.ProEt) (V : X.ProEt) :
    (siteInclude U).obj ((proEtaleBaseChange U.hom).obj V) ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom U.hom) pullback.condition

/-- Restriction to an arbitrary object of the site. The slice equivalence and ring map
are fixed by the actual inclusion and evaluation of continuous functions. The last
comparison identifies ordinary module inverse image with literal site restriction.
Source: BS 6.8.14 and 6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure SiteRestriction (X : Scheme.{u}) (U : X.ProEt) where
  slice : U.left.ProEt ≌ Over U
  slice_normalization : slice.functor ⋙ Over.forget U = siteInclude U
  [continuous : slice.functor.IsContinuous (ProEt.topology U.left) ((ProEt.topology X).over U)]
  ring : ((adicLisseForget U.left).obj (rationalCoefficientSheaf l U.left E)) ≅
    (slice.functor.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U.left) ((ProEt.topology X).over U)).obj
        (((adicLisseForget X).obj (rationalCoefficientSheaf l X E)).over U)
  ring_normalization : ∀ (V : U.left.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l U.left E).obj.obj V),
    HEq (ring.hom.hom.app V s) s
  coefficient : (adicTowerInverseImage U.hom).obj (rationalCoefficientSheaf l X E) ⟶
    rationalCoefficientSheaf l U.left E
  normalized : rationalCoefficientRestrictionNormalized l E U.hom coefficient
  coefficient_iso : IsIso coefficient
  comparison : modulePull U.hom coefficient ≅
    SheafOfModules.overFunctor
      ((adicLisseForget X).obj (rationalCoefficientSheaf l X E)) U ⋙
        SheafOfModules.pushforward (F := slice.functor) (J := ProEt.topology U.left)
          (K := (ProEt.topology X).over U) ring.hom
  comparison_units : ∀ (M : pbcModules X (rationalCoefficientSheaf l X E))
      (V : X.ProEt) (m : M.val.obj (op V)),
    HEq ((comparison.hom.app M).val.app (op ((proEtaleBaseChange U.hom).obj V))
      (moduleUnit U.hom coefficient M V m)) (M.val.map (siteCounit U V).op m)
  [ordinaryAdditive : (modulePull U.hom coefficient).Additive]
  [exact_limits : PreservesFiniteLimits (modulePull U.hom coefficient)]
  [exact_colimits : PreservesFiniteColimits (modulePull U.hom coefficient)]
  counit : DerivedCategory.Q ⋙ derivedPull U.hom coefficient ⟶
    (modulePull U.hom coefficient).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  normalized_counit : IsNormalizedPullCounit U.hom coefficient counit
  universal : (derivedPull U.hom coefficient).IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso _ (.up ℤ))
  derived : derivedPull U.hom coefficient ≅ (modulePull U.hom coefficient).mapDerivedCategory
  derived_normalization : ∀ P,
    derived.hom.app (DerivedCategory.Q.obj P) ≫
        (modulePull U.hom coefficient).mapDerivedCategoryFactors.hom.app P = counit.app P

/-- A compatible family of realizations. All fields, embeddings, schemes and morphisms
are quantified, so the identity, composition and mixed comparison clauses refer to
one family rather than unrelated existence witnesses.
Source: BS 6.8.14--6.8.15 (blueprint: lem-per-continuous-rational-derived-realization). -/
structure Family (l : ℕ) [Fact l.Prime] where
  realization : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : Base.{u} l), At l A X
  along : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme), Along l A g (realization A X) (realization A Y)
  composition : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y Z : Base.{u} l} (g : X.scheme ⟶ Y.scheme) (h : Z.scheme ⟶ X.scheme),
    Composition l A g h (realization A X) (realization A Y) (realization A Z)
      (along A g) (along A h) (along A (h ≫ g))
  identity : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (X : Base.{u} l), Identity l A X (realization A X) (along A (𝟙 X.scheme))
  fieldChange : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : Base.{u} l), FieldChange l A B i X (realization A X) (realization B X)
  fieldComposition : ∀ (A B C : Type u) [Field A] [Field B] [Field C]
    [Algebra ℚ_[l] A] [Algebra ℚ_[l] B] [Algebra ℚ_[l] C]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    [FiniteDimensional ℚ_[l] C]
    (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C) (X : Base.{u} l),
    FieldComposition l A B C i j X (realization A X) (realization B X) (realization C X)
      (fieldChange A B i X) (fieldChange B C j X) (fieldChange A C (j.comp i) X)
  mixed : ∀ (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme),
    Mixed l A B i g (realization A X) (realization A Y) (realization B X) (realization B Y)
      (along A g) (along B g) (fieldChange A B i X) (fieldChange A B i Y)
  siteRestriction : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X : Base.{u} l) (U : X.scheme.ProEt),
    SiteRestriction l A X.scheme U

end AlgebraicGeometry.Scheme.ContinuousRational
