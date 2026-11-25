/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
public import WeilConjectures.Algebra.Homology.KFlatRoos.KFlatRoosRepresentativeInvariance
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
/-! # Strict completion comparison interface

Source: blueprint main-20261015, localizing-closure finite-model proof, Locality;
Stacks Tags 09AA, 03EK, 014E and 08TC
(blueprint: def-sfb-strict-completion-restriction-data).

The presentation structures below only package the assertions of this node. Cone
objects, coordinates, tower arrows, Roos functor, augmentations and localized units
are all fixed by equations. No comparison or completion is selected from existence.
Positive exponent n+1 is indexed by n : ℕ, as in the recorded completion interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b c d w z
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures
open CategoryTheory.InternalAbelianSheafModule

namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules


/-- The existing small-site local-equivalence instance with its unused larger
coefficient universe fixed to zero, so inference keeps the prescribed universe.
Source: Stacks 00W1, 03DA; strict Roos comparison
(blueprint: lem-sfb-strict-completion-restriction-comparison). -/
instance smallSiteLocalEquivalences (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  surjectiveTower_wEqualsLocallyBijective.{u, 0} X

/-- The concrete strict scalar-cone tower and its normalized completion descent.
Source: blueprint Locality and first-reduction Cones paragraphs; Stacks 014E, 08TC
(blueprint: lem-sfb-strict-completion-restriction-comparison). -/
structure Presentation (A : Type a) [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasDerivedCategory.{w} A] where
  scalar : End (𝟭 A)
  tower : CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ
  cone : ∀ (M : CochainComplex A ℤ) (n : ℕ),
    (tower.obj M).asFunctor.obj (op n) = CochainComplex.mappingCone
      ((NatTrans.mapHomologicalComplex (scalar ^ (n + 1)).asHom (.up ℤ)).app M)
  coordinates : ∀ (M : CochainComplex A ℤ) (n : ℕ) (q : ℤ),
    ((tower.obj M).asFunctor.obj (op n)).X q ≅ M.X q ⊞ M.X (q + 1)
  coordinates_eq : ∀ (M : CochainComplex A ℤ) (n : ℕ) (q : ℤ),
    coordinates M n q = eqToIso (congrArg (fun K ↦ K.X q) (cone M n)) ≪≫
      principalConeCoordinates
        ((NatTrans.mapHomologicalComplex (scalar ^ (n + 1)).asHom (.up ℤ)).app M) q
  diagonal : ∀ {M N : CochainComplex A ℤ} (f : M ⟶ N) (n : ℕ) (q : ℤ),
    ((tower.map f).f q).app (op n) ≫ (coordinates N n q).hom =
      (coordinates M n q).hom ≫ biprod.map (f.f q) (f.f (q + 1))
  transition : ∀ (M : CochainComplex A ℤ) (n : ℕ) (q : ℤ),
    ((tower.obj M).asFunctor.map (homOfLE (Nat.le_succ n)).op).f q ≫
        (coordinates M n q).hom =
      (coordinates M (n + 1) q).hom ≫ biprod.map (𝟙 _) (scalar.asHom.app (M.X (q + 1)))
  augmentation : 𝟭 (CochainComplex A ℤ) ⟶ tower ⋙ roosF
  augmentation_zero : ∀ (M : CochainComplex A ℤ) (p : ℤ),
    (augmentation.app M).f (p + 1) ≫ (roosχ (tower.obj M) p).hom ≫ biprod.fst = 0
  augmentation_level : ∀ (M : CochainComplex A ℤ) (n : ℕ) (p : ℤ),
    (augmentation.app M).f (p + 1) ≫ (roosχ (tower.obj M) p).hom ≫ biprod.snd ≫
        (Pi.π (fun i : ℕ ↦ (tower.obj M).asFunctor.obj (op i)) n).f (p + 1) ≫
        (coordinates M n (p + 1)).hom = biprod.inl
  reduction : ℕ → DerivedCategory.{w} A ⥤ DerivedCategory.{w} A
  reduction_descent : ∀ n : ℕ,
    DerivedCategory.Q ⋙ reduction n ≅ tower ⋙
      ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  reduction_step : ∀ n : ℕ, reduction (n + 1) ⟶ reduction n
  reduction_unit : ∀ n : ℕ, 𝟭 (DerivedCategory.{w} A) ⟶ reduction n
  reduction_step_descent : ∀ (n : ℕ) (M : CochainComplex A ℤ),
    (reduction_step n).app (DerivedCategory.Q.obj M) ≫
        (reduction_descent n).hom.app M =
      (reduction_descent (n + 1)).hom.app M ≫
        DerivedCategory.Q.map ((tower.obj M).asFunctor.map
          (homOfLE (Nat.le_succ n)).op)
  reduction_unit_descent : ∀ (n : ℕ) (M : CochainComplex A ℤ),
    (reduction_unit n).app (DerivedCategory.Q.obj M) ≫
        (reduction_descent n).hom.app M =
      DerivedCategory.Q.map (augmentation.app M ≫ roosEval (tower.obj M) n)
  completion : DerivedCategory.{w} A ⥤ DerivedCategory.{w} A
  unit : 𝟭 (DerivedCategory.{w} A) ⟶ completion
  descent : DerivedCategory.Q ⋙ completion ≅ tower ⋙ roosF ⋙ DerivedCategory.Q
  unit_descent : ∀ M : CochainComplex A ℤ,
    unit.app (DerivedCategory.Q.obj M) ≫ descent.hom.app M =
      DerivedCategory.Q.map (augmentation.app M)

/-- One simultaneous comparison, fixed on principal cones, product projections,
Roos coordinates, augmentations, and derived representatives.
Source: blueprint Locality, expanded strict completion calculation
(blueprint: lem-sfb-strict-completion-restriction-comparison). -/
structure Comparison
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory.{w} A]
    {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]
    [HasDerivedCategory.{z} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : Presentation A) (T : Presentation B) where
  homology : ∀ q : ℤ, DerivedCategory.homologyFunctor A q ⋙ F ≅
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B q
  homology_eq : ∀ q : ℤ, homology q = F.mapDerivedCategoryHomologyFunctorIso q
  scalar : ∀ M : A, F.map (S.scalar.asHom.app M) = T.scalar.asHom.app (F.obj M)
  tower : S.tower ⋙
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ T.tower
  tower_coordinates : ∀ (M : CochainComplex A ℤ) (n : ℕ) (q : ℤ),
    ((tower.hom.app M).f q).app (op n) ≫
        (T.coordinates ((F.mapHomologicalComplex (.up ℤ)).obj M) n q).hom =
      F.map (S.coordinates M n q).hom ≫ F.biprodComparison (M.X q) (M.X (q + 1))
  product : ∀ M : CochainComplex A ℤ,
    (F.mapHomologicalComplex (.up ℤ)).obj (roosP (S.tower.obj M)) ≅
      roosP (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M))
  product_projection : ∀ (M : CochainComplex A ℤ) (n : ℕ) (q : ℤ),
    (product M).hom.f q ≫
        (Pi.π (fun i : ℕ ↦
          (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)).asFunctor.obj (op i))
          n).f q =
      F.map ((Pi.π (fun i : ℕ ↦ (S.tower.obj M).asFunctor.obj (op i)) n).f q) ≫
        ((tower.hom.app M).f q).app (op n)
  roos_map : ∀ M : CochainComplex A ℤ,
    (F.mapHomologicalComplex (.up ℤ)).map (roosU (S.tower.obj M)) ≫ (product M).hom =
      (product M).hom ≫ roosU (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M))
  chain : S.tower ⋙ roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ T.tower ⋙ roosF
  chain_coordinates : ∀ (M : CochainComplex A ℤ) (p : ℤ),
    (chain.hom.app M).f (p + 1) ≫
        (roosχ (T.tower.obj ((F.mapHomologicalComplex (.up ℤ)).obj M)) p).hom =
      F.map (roosχ (S.tower.obj M) p).hom ≫
        F.biprodComparison ((roosP (S.tower.obj M)).X p)
          ((roosP (S.tower.obj M)).X (p + 1)) ≫
        biprod.map ((product M).hom.f p) ((product M).hom.f (p + 1))
  chain_unit : ∀ M : CochainComplex A ℤ,
    (F.mapHomologicalComplex (.up ℤ)).map (S.augmentation.app M) ≫ chain.hom.app M =
      T.augmentation.app ((F.mapHomologicalComplex (.up ℤ)).obj M)
  reduction : ∀ n : ℕ,
    S.reduction n ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ T.reduction n
  reduction_representative : ∀ (n : ℕ) (M : CochainComplex A ℤ),
    (reduction n).hom.app (DerivedCategory.Q.obj M) ≫
        (T.reduction n).map (F.mapDerivedCategoryFactors.hom.app M) ≫
        (T.reduction_descent n).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
      F.mapDerivedCategory.map ((S.reduction_descent n).hom.app M) ≫
        F.mapDerivedCategoryFactors.hom.app ((S.tower.obj M).asFunctor.obj (op n)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (tower.hom.app M)).app (op n))
  reduction_transition : ∀ (n : ℕ) (K : DerivedCategory.{w} A),
    F.mapDerivedCategory.map ((S.reduction_step n).app K) ≫ (reduction n).hom.app K =
      (reduction (n + 1)).hom.app K ≫
        (T.reduction_step n).app (F.mapDerivedCategory.obj K)
  reduction_augmentation : ∀ (n : ℕ) (K : DerivedCategory.{w} A),
    F.mapDerivedCategory.map ((S.reduction_unit n).app K) ≫ (reduction n).hom.app K =
      (T.reduction_unit n).app (F.mapDerivedCategory.obj K)
  derived : S.completion ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ T.completion
  representative : ∀ M : CochainComplex A ℤ,
    derived.hom.app (DerivedCategory.Q.obj M) ≫
        T.completion.map (F.mapDerivedCategoryFactors.hom.app M) ≫
        T.descent.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj M) =
      F.mapDerivedCategory.map (S.descent.hom.app M) ≫
        F.mapDerivedCategoryFactors.hom.app (roosF.obj (S.tower.obj M)) ≫
        DerivedCategory.Q.map (chain.hom.app M)
  unit : ∀ K : DerivedCategory.{w} A,
    F.mapDerivedCategory.map (S.unit.app K) ≫ derived.hom.app K =
      T.unit.app (F.mapDerivedCategory.obj K)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Agreement with the specified internal completion, including every K-flat
realization of its canonical map. The strict tower is the dependency's actual tower.
Source: blueprint first-reduction Cones paragraph and completion triangle comparison
(blueprint: lem-sfb-strict-completion-restriction-comparison). -/
def IsIntegral (X : Scheme.{u})
    (S : Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E X)) : Prop :=
  ∃ data : PrincipalReduction.PrincipalReductionConeData l E X,
    data.IsCanonical l E X ∧ S.tower = CompletionTriangle.tower l E X data ∧
    S.scalar.asHom = DerivedNakayama.scalarOnModules l E X data.d ∧
    (∀ n : ℕ, S.reduction n = PrincipalReduction.reductionFunctor l E X n) ∧
    (∀ (n : ℕ) (K : DerivedCategory (AdicCompletion.Modules l E X)),
      HEq ((S.reduction_unit n).app K)
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient l E X n)).unit.app K) ∧
      HEq ((S.reduction_step n).app K) (AdicCompletion.integralStep l E X K n)) ∧
    ∀ (K : DerivedCategory (AdicCompletion.Modules l E X))
      (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
      (_hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E X) (.up ℤ)).kFlat P)
      (e : DerivedCategory.Q.obj P ≅ K),
      ∃ ψ : S.completion.obj K ≅ DerivedCategory.Q.obj (AdicCompletion.roos l E X P),
        S.unit.app K ≫ ψ.hom = AdicCompletion.completionMap l E X K P e

/-- A constant scalar, evaluated in the actual section ring after pullback.
Endomorphisms of the regular point-module are exactly its constant scalars.
Source: blueprint Locality, finite scalar presentations; Stacks 03EK
(blueprint: lem-sfb-strict-completion-restriction-comparison). -/
def sectionScalarValue (X : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) (U : X.ProEtᵒᵖ) :
    (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X).obj.obj U :=
  (((DerivedNakayama.regularPullbackIso l E X).inv ≫
    (DerivedNakayama.pullback l E X).map d.asHom ≫
    (DerivedNakayama.regularPullbackIso l E X).hom).hom.hom.app U)
      (1 : (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X).obj.obj U)

/-- Finite biproducts from the existing finite products of section-module sheaves.
Source: Stacks 03DB (blueprint: lem-sfb-strict-completion-restriction-comparison). -/
instance sectionFiniteBiproducts (X : Scheme.{u}) :
    HasFiniteBiproducts
      (ModuleObjectRingedComparison.Modules (DerivedNakayama.integerRing l E) X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Section-module local models use the actual ringed inverse image and cokernels
of finite matrices whose entries are scalars on the point. Neither local object
is obtained by applying the section equivalence to an internal local-model isomorphism.
Source: blueprint Local models and Locality; Stacks 03D7, 03EK
(blueprint: lem-sfb-strict-completion-restriction-comparison). -/
def HasSectionFiniteConstantLocalModel (X : Scheme.{u})
    (M : ModuleObjectRingedComparison.Modules (DerivedNakayama.integerRing l E) X) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ (m n : ℕ) (a : Fin m → Fin n → End (Mod.regular (DerivedNakayama.integerRing l E)))
      (f : (⨁ fun _ : Fin m ↦ SheafOfModules.unit
          ((sheafCompose (Scheme.ProEt.topology (𝒰.X i))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) (𝒰.X i)))) ⟶
        (⨁ fun _ : Fin n ↦ SheafOfModules.unit
          ((sheafCompose (Scheme.ProEt.topology (𝒰.X i))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) (𝒰.X i))))),
      (∀ (j : Fin m) (k : Fin n) (U : (𝒰.X i).ProEtᵒᵖ)
        (x : (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E)
          (𝒰.X i)).obj.obj U),
        ((biproduct.ι _ j ≫ f ≫ biproduct.π _ k).val.app U) x =
          sectionScalarValue l E (𝒰.X i) (a j k) U * x) ∧
      Nonempty ((InternalModuleOperations.upperStar (DerivedNakayama.integerRing l E)
        (𝒰.f i)).obj M ≅ cokernel f)

open ModuleObjectRingedComparison

-- Keep the tensor-unit construction folded while checking the reduction interface.
-- Explicit identity-complex transport avoids rechecking that large tensor expression.
attribute [local irreducible] SheafOfModules.KFlatRoos.tensorUnit
  SheafOfModules.siteSheafTensorRight
  SheafOfModules.KFlatRoos.roos coefficientTotalTensor
  SheafOfModules.siteSheafTensorTmul coefficientTensorGenerator

/-- The section reductions are derived extension to the specified quotient, followed
by restriction. Their tensor identifications are fixed on K-flat representatives:
resolving the quotient in the second slot gives the section TensorComparison model.
The singleton total comparison is fixed on every local pure tensor, so the unit
and transition equations cannot be changed by a scalar twist.
Source: blueprint Locality, steps 4--7; Stacks 03EK, 06YS, 08TC
(blueprint: lem-sfb-strict-completion-restriction-comparison). -/
structure SectionReductionModelsFor
    (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (T : Presentation.{u + 2, u + 1, u + 1}
      (SheafOfModules ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (H : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
      (Scheme.ProEt.topology X) R))
    (HM : CoefficientTensorModels.{u, u + 1, u, u + 1} (Scheme.ProEt.topology X)
      R H)
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (ι : (Functor.const ℕᵒᵖ).obj R ⟶ B) where
  single : ∀ (n : ℕ) (P : CochainComplex (SheafOfModules ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ),
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
      R).obj
        (P, (CochainComplex.singleFunctor _ 0).obj
          (SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι n)) ≅
      (SheafOfModules.KFlatRoos.level.{u + 1, u, u + 1} B ι n).obj P
  single_values : ∀ (n : ℕ)
    (P : CochainComplex (SheafOfModules ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (p : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X p).val.obj U)
    (y : (SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι n).val.obj U),
    ((single n P).hom.f p).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X)
        R P
        ((CochainComplex.singleFunctor _ 0).obj
          (SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι n))
        p 0 p (add_zero p)
        U x ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι n)).inv.val.app U y)) =
      SheafOfModules.siteSheafTensorTmul (P.X p)
        (SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι n) U x y
  tensor : ∀ n : ℕ, T.reduction n ≅
    Prod.sectL _ (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ 0).obj
        (SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι n))) ⋙ H.tensor
  model : ∀ (n : ℕ)
    (P : CochainComplex (SheafOfModules ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := R) P),
    (T.reduction n).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((SheafOfModules.KFlatRoos.level.{u + 1, u, u + 1} B ι n).obj P)
  unit : ∀ (n : ℕ)
    (P : CochainComplex (SheafOfModules ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := R) P),
    (T.reduction_unit n).app (DerivedCategory.Q.obj P) ≫ (model n P hP).hom =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
          (SheafOfModules.KFlatRoos.tensorUnit.{u + 1, u, u + 1} (ι.app (op n))) (.up ℤ)).app P)
  step : ∀ (n : ℕ)
    (P : CochainComplex (SheafOfModules ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := R) P),
    (T.reduction_step n).app (DerivedCategory.Q.obj P) ≫ (model n P hP).hom =
      (model (n + 1) P hP).hom ≫
        DerivedCategory.Q.map (SheafOfModules.KFlatRoos.transition.{u + 1, u, u + 1} B ι P n)
  tensor_model : ∀ (n : ℕ)
    (P Q : CochainComplex (SheafOfModules ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := R) Q)
    (q : Q ⟶ (CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι n))
    (_hq : QuasiIso q),
    HEq (DerivedCategory.Q.map
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
          R).map
          (X := (P, Q))
          (Y := (P, (CochainComplex.singleFunctor _ 0).obj
            (SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι n)))
          (𝟙 P, q) ≫ (single n P).hom) ≫
        (model n P hP).inv ≫ (tensor n).hom.app (DerivedCategory.Q.obj P))
      ((CoefficientTensorModels.iso (Scheme.ProEt.topology X)
        R H HM P Q hP hQ).hom ≫
        H.tensor.map (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
          (Y := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor _ 0).obj
              (SheafOfModules.KFlatRoos.levelModule.{u + 1, u, u + 1} B ι n))))
          (𝟙 _, DerivedCategory.Q.map q))

/-- The normalized section reduction models at the integral coefficient ring.
Source: blueprint Locality, steps 4--7; Stacks 03EK, 06YS, 08TC
(blueprint: def-sfb-strict-completion-restriction-data).
This is the generic interface specialized to the fixed coefficient ring. -/
abbrev SectionReductionModels (X : Scheme.{u})
    (T : Presentation.{u + 2, u + 1, u + 1} (Modules (DerivedNakayama.integerRing l E) X))
    (H : CoefficientClosedStructure (hom (DerivedNakayama.integerRing l E) X))
    (HM : CoefficientTensorModels.{u, u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (ring (DerivedNakayama.integerRing l E) X) H)
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (ι : (Functor.const ℕᵒᵖ).obj (ring (DerivedNakayama.integerRing l E) X) ⟶ B) :=
  SectionReductionModelsFor X (ring (DerivedNakayama.integerRing l E) X) T H HM B ι

/-- Integral completion on the section-ring side, fixed independently of transport
of a Presentation by an equivalence. The scalar is the pulled-back uniformizer;
the coefficient tower, its structure maps and steps are the actual section rings
and quotient homomorphisms. The reduction models use the existing section derived
tensor comparison, normalized on K-flats. Completion and its unit are the actual
augmented tensor Roos construction on every section K-flat representative.
Source: blueprint Locality and completion Cones paragraph; Stacks 03EK, 06YS, 08TC
(blueprint: lem-sfb-strict-completion-restriction-comparison). -/
def IsSectionIntegral (X : Scheme.{u})
    (T : Presentation.{u + 2, u + 1, u + 1} (Modules (DerivedNakayama.integerRing l E) X)) :
    Prop :=
  ∃ data : PrincipalReduction.PrincipalReductionConeData l E X,
    data.IsCanonical l E X ∧
    (∀ (M : Modules (DerivedNakayama.integerRing l E) X) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U),
      (T.scalar.asHom.app M).val.app U x = sectionScalarValue l E X data.d U • x) ∧
    ∃ (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
      (ι : (Functor.const ℕᵒᵖ).obj (ring (DerivedNakayama.integerRing l E) X) ⟶ B),
      (∀ n : ℕ, B.obj (op n) = sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (AdicCompletion.finiteRing l E X n)) ∧
      (∀ n : ℕ, HEq (ι.app (op n))
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.quotient l E X n))) ∧
      (∀ n : ℕ, HEq (B.map (homOfLE (Nat.le_succ n)).op)
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (AdicCompletion.transition l E X n))) ∧
      (∃ (H : CoefficientClosedStructure (hom (DerivedNakayama.integerRing l E) X))
        (HM : CoefficientTensorModels.{u, u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (ring (DerivedNakayama.integerRing l E) X) H),
        Nonempty (TensorComparison (DerivedNakayama.integerRing l E) X H HM) ∧
        Nonempty (SectionReductionModels l E X T H HM B ι)) ∧
      ∀ (K : DerivedCategory (Modules (DerivedNakayama.integerRing l E) X))
        (P : CochainComplex (Modules (DerivedNakayama.integerRing l E) X) ℤ)
        (_hP : CochainComplex.IsKFlatIndependentCoefficients
          (R := ring (DerivedNakayama.integerRing l E) X) P)
        (e : DerivedCategory.Q.obj P ≅ K),
        ∃ ψ : T.completion.obj K ≅
            DerivedCategory.Q.obj (SheafOfModules.KFlatRoos.roos.{u + 1, u, u + 1} B ι P),
          T.unit.app K ≫ ψ.hom = e.inv ≫
            DerivedCategory.Q.map (SheafOfModules.KFlatRoos.augmentation.{u + 1, u, u + 1} B ι P)

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
