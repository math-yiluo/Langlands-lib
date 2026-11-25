/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCompactSupportUniformRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedConstructiblePreservation
import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Compact-support base change over a finite extension

Source: blueprint main-20261015, `thm-cbc-finite-extension`, order 1991
(blueprint: thm-cbc-finite-extension).

The integral compact-support exchange is transported through the raw scalar
localization.  The source and target are the completed compact-support
composites attached to the chosen compactifications; the displayed naturality
equation is the naturality required for every rational morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local irreducible] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

private instance finiteExtension_reductionModuleLinear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    Linear A (reductionModules T (completedReductionCoefficient T d)) :=
  pbcCompletedModulesLinear T d

private instance finiteExtension_derivedLinear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    Linear A (d.derived T) := pbcCompletedDerivedLinear T d

private instance finiteExtension_towerLinear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    Linear A (d.towers T) :=
  inferInstanceAs (Linear A (ℕᵒᵖ ⥤ proEtaleRingModules T (d.completedRing T)))

private instance finiteExtension_derivedTowerLinear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    Linear A (DerivedCategory (d.towers T)) :=
  inferInstanceAs (Linear A (DerivedCategory (ℕᵒᵖ ⥤
    proEtaleRingModules T (d.completedRing T))))

attribute [local irreducible] completedReductionTower Functor.mapDerivedCategory

/-- Scalar multiplication descends through a universal left-derived pair. -/
private theorem finiteExtension_kan_linear
    {R : Type*} [CommRing R]
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Preadditive C] [Preadditive D] [Preadditive B]
    [Linear R C] [Linear R D] [Linear R B]
    (Q : C ⥤ D) [Q.Linear R] (F : C ⥤ B) [F.Linear R]
    (L : D ⥤ B) (epsilon : Q ⋙ L ⟶ F) [L.IsRightKanExtension epsilon] :
    L.Linear R := by
  rw [Functor.linear_iff]
  intro X r
  let gamma : L ⟶ L :=
    { app := fun Y ↦ L.map (r • 𝟙 Y)
      naturality := fun Y Z f ↦ by
        simp only [← L.map_comp, Linear.comp_smul, Linear.smul_comp,
          Category.comp_id, Category.id_comp] }
  let delta : L ⟶ L :=
    { app := fun Y ↦ r • 𝟙 (L.obj Y)
      naturality := fun Y Z f ↦ by simp }
  have he : gamma = delta := by
    apply L.hom_ext_of_isRightKanExtension epsilon
    ext Y
    have hn := epsilon.naturality (r • 𝟙 Y)
    change L.map (r • 𝟙 (Q.obj Y)) ≫ epsilon.app Y =
      (r • 𝟙 (L.obj (Q.obj Y))) ≫ epsilon.app Y
    simpa using hn
  exact congrArg (fun t : L ⟶ L ↦ t.app X) he

/-- The strict ordinary reduction tower respects constant scalars. -/
private theorem finiteExtension_reduction_linear
    {A : Type (u + 1)} [CommRing A] (T : Scheme.{u}) (d : AdicCoefficientDatum A) :
    (completedReductionModuleTowerFunctor T d).Linear A := by
  constructor
  intro M N f a
  apply NatTrans.ext
  funext n
  let phi := completedReductionProjection T d n.unop
  apply level_hom_ext T phi M ((completedReductionLevel T d n.unop).obj N)
  intro U t x
  change ((reductionChange T phi).map (a • f)).val.app U
      (reductionTensorSection T phi M U t x) =
    phi.hom.app U (pbcCompletedSection T d U a) •
      ((reductionChange T phi).map f).val.app U (reductionTensorSection T phi M U t x)
  rw [reductionTensor_map, reductionTensor_map]
  change reductionTensorSection T phi N U t (pbcCompletedSection T d U a • f.val.app U x) = _
  let eta := reductionUnit T phi N
  have heta := (eta.val.app U).hom.map_smul (pbcCompletedSection T d U a) (f.val.app U x)
  change eta.val.app U (pbcCompletedSection T d U a • f.val.app U x) =
    phi.hom.app U (pbcCompletedSection T d U a) •
      (show ((reductionChange T phi).obj N).val.obj U from eta.val.app U (f.val.app U x))
    at heta
  rw [reductionUnit_apply, reductionUnit_apply] at heta
  have ht (y : N.val.obj U) := tensorSection_smul T phi N U t 1 y
  simp only [mul_one] at ht
  change _ = phi.hom.app U (pbcCompletedSection T d U a) •
    (show ((reductionChange T phi).obj N).val.obj U from
      reductionTensorSection T phi N U t (f.val.app U x))
  calc
    _ = t • reductionTensorSection T phi N U 1
        (pbcCompletedSection T d U a • f.val.app U x) := (ht _).symm
    _ = t • (phi.hom.app U (pbcCompletedSection T d U a) •
        reductionTensorSection T phi N U 1 (f.val.app U x)) := congrArg (t • ·) heta
    _ = phi.hom.app U (pbcCompletedSection T d U a) •
        (t • reductionTensorSection T phi N U 1 (f.val.app U x)) := smul_comm _ _ _
    _ = _ := congrArg (phi.hom.app U (pbcCompletedSection T d U a) • ·) (ht _)

/-- Ambient completed pullback preserves the specified constant-section action. -/
private theorem finiteExtension_completedPull_linear
    {A : Type (u + 1)} [CommRing A] {U V : Scheme.{u}}
    (d : AdicCoefficientDatum A) (f : U ⟶ V) : (d.completedPull f).Linear A := by
  have := finiteExtension_reduction_linear V d
  have : (completedReductionHomotopyFunctor V d).Linear A := by
    unfold completedReductionHomotopyFunctor
    infer_instance
  have := (completedReductionTower_properties V d).1
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension
    (completedReductionTower V d) (coherenceReductionTowerCounit V d)
    (HomotopyCategory.quasiIso _ (.up ℤ))
  have : (completedReductionTower V d).Linear A :=
    finiteExtension_kan_linear DerivedCategory.Qh (completedReductionHomotopyFunctor V d)
      (completedReductionTower V d) (coherenceReductionTowerCounit V d)
  have : (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).Linear A := by
    rw [← coefficientIso_eq f d]
    exact completedModulePushLinear f d
  have : (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).Linear A :=
    (proEtaleRingModuleAdjunction f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).left_adjoint_linear
  have : (d.towerModulePull f).Linear A := by
    constructor
    intro M N v a
    apply NatTrans.ext
    funext n
    exact Functor.map_smul
      (proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U)
        (d.integralRingIso f)) a (v.app n)
  have : (d.constantTower U).Linear A := by
    constructor
    intro M N v a
    apply NatTrans.ext
    funext n
    rfl
  have : (d.derivedConstantTower U).Linear A := by
    unfold AdicCoefficientDatum.derivedConstantTower
    infer_instance
  have : (completedRlim U (d.completedRing U)).Linear A :=
    (d.constantRlimAdjunction U).right_adjoint_linear
  unfold AdicCoefficientDatum.completedPull
  infer_instance

/-- Open extension and direct image respect constant scalars by their adjunctions. -/
private theorem finiteExtension_open_linear
    {A : Type (u + 1)} [CommRing A] {U T : Scheme.{u}}
    (d : AdicCoefficientDatum A) (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcDerivedOpenShriek d j hj).Linear A := by
  let := hj
  have : (proEtaleRingModuleDirectImage j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).Linear A := by
    rw [← coefficientIso_eq j d]
    exact completedModulePushLinear j d
  have : (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).Linear A :=
    (proEtaleRingModuleAdjunction j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).left_adjoint_linear
  have := cbcPullToRestriction_isIso d j
  have : (cbcOpenRestriction d j hj).Linear A :=
    Functor.linear_of_iso A (asIso (cbcPullToRestriction d j))
  have : (cbcOpenShriek d j hj).Linear A := (cbcOpenAdjunction d j hj).left_adjoint_linear
  unfold cbcDerivedOpenShriek
  infer_instance

private theorem finiteExtension_push_linear
    {A : Type (u + 1)} [CommRing A] {U V : Scheme.{u}}
    (d : AdicCoefficientDatum A) (f : U ⟶ V) : (d.push f).Linear A := by
  have : (proEtaleRingModuleDirectImage f (d.completedRing V) (d.completedRing U)
      (d.integralRingIso f)).Linear A := by
    rw [← coefficientIso_eq f d]
    exact completedModulePushLinear f d
  unfold AdicCoefficientDatum.push proEtaleRingDerivedDirectImage
  infer_instance

/-- Additivity interface needed by scalar transport for the completed open operation.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension).
Proof: extension by zero is additive on module sections. Its exact termwise functor
respects sums of chain maps, and the equation descends through the derived localization. -/
@[instance] theorem cbcDerivedOpenShriek_additive
    {A : Type (u + 1)} [CommRing A] {U T : Scheme.{u}}
    (d : AdicCoefficientDatum A) (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcDerivedOpenShriek d j hj).Additive := by
  unfold cbcDerivedOpenShriek
  infer_instance

/-- Additivity interface needed by scalar transport for completed pullback.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension).
Proof: the reduction-tower construction and derived tower pullback respect sums on
representatives; derived inverse limit is additive. Compose these three equations. -/
@[instance] theorem completedPull_additive
    {A : Type (u + 1)} [CommRing A] {U V : Scheme.{u}}
    (d : AdicCoefficientDatum A) (f : U ⟶ V) :
    (d.completedPull f).Additive := by
  obtain ⟨shift, tri⟩ := (completedReductionTower_properties V d).2.1
  let := shift
  have := tri
  have : (completedReductionTower V d).Additive := inferInstance
  unfold AdicCoefficientDatum.completedPull
  infer_instance

/-- The source composite is additive.
Proof: extension by zero, derived direct image, and completed pullback are additive
on representative maps. Composition preserves these addition equations.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportSource_additive
    {A : Type (u + 1)} [CommRing A] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (g : Y' ⟶ Y) (c : Compactification f) (d : AdicCoefficientDatum A) :
    (cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g ⋙ d.completedPull g).Additive := by
  infer_instance

/-- The target composite is additive.
Proof: completed pullback, extension by zero, and derived direct image are additive
on representative maps. Composition preserves these addition equations.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportTarget_additive
    {A : Type (u + 1)} [CommRing A] {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
    (g' : X' ⟶ X) (c' : Compactification f') (d : AdicCoefficientDatum A) :
    (d.completedPull g' ⋙ cbcDerivedOpenShriek d c'.i c'.isOpenImmersion ⋙
      d.push c'.g).Additive := by
  have := completedPull_additive d g'
  have := cbcDerivedOpenShriek_additive d c'.i c'.isOpenImmersion
  infer_instance

/-- The source compact-support composite in the chosen compactification.
Source: `def-cbc-completed-exchange-map` (blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportSource
    {A : Type (u + 1)} [CommRing A] {X Y Y' : Scheme.{u}}
    {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum A) :=
  cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g ⋙ d.completedPull g

/-- The target compact-support composite in the chosen compactification.
Source: `def-cbc-completed-exchange-map` (blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportTarget
    {A : Type (u + 1)} [CommRing A] {X X' Y' : Scheme.{u}}
    {f' : X' ⟶ Y'} (g' : X' ⟶ X) (c' : Compactification f')
    (d : AdicCoefficientDatum A) :=
  d.completedPull g' ⋙ cbcDerivedOpenShriek d c'.i c'.isOpenImmersion ⋙ d.push c'.g

/-- The source lift whose objects retain the constructibility witness.
Source: the integral category restriction in the proof
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportSourceLift
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    PbcBoundedConstructibleComplete X d ⥤
      PbcBoundedConstructibleComplete Y' d :=
  by
    letI := cbcCompactSupportSource_additive g c d
    exact ObjectProperty.liftFullSubcategory
      (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
      (cbcCompactSupportSource g c d) (fun K hK ↦ hSource ⟨K, hK⟩)

/-- The target lift whose objects retain the constructibility witness.
Source: the integral category restriction in the proof
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportTargetLift
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    PbcBoundedConstructibleComplete X d ⥤
      PbcBoundedConstructibleComplete Y' d :=
  by
    letI := cbcCompactSupportTarget_additive g' c' d
    exact ObjectProperty.liftFullSubcategory
      (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
      (cbcCompactSupportTarget g' c' d) (fun K hK ↦ hTarget ⟨K, hK⟩)

/-- The source restriction is additive for the inherited full-subcategory addition.
Proof: the restriction maps each morphism by the ambient composite. Its additivity
equation is the ambient equation viewed through the faithful full inclusion.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportSourceLift_additive
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    (cbcCompactSupportSourceLift l E g c d hSource).Additive := by
  have := cbcCompactSupportSource_additive g c d
  constructor
  intro M N f h
  apply ObjectProperty.hom_ext
  exact Functor.map_add (cbcCompactSupportSource g c d)

/-- The target restriction is additive for the inherited full-subcategory addition.
Proof: the restriction maps each morphism by the ambient composite. Its additivity
equation is the ambient equation viewed through the faithful full inclusion.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportTargetLift_additive
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    (cbcCompactSupportTargetLift l E g' c' d hTarget).Additive := by
  have := cbcCompactSupportTarget_additive g' c' d
  constructor
  intro M N f h
  apply ObjectProperty.hom_ext
  exact Functor.map_add (cbcCompactSupportTarget g' c' d)

/-- The source restriction respects the actual constant-section scalar action.
Proof: tensor, pullback and direct image commute with scalar multiples of maps on
representatives. These equations survive localization and full-subcategory restriction.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportSourceLift_linear
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    (cbcCompactSupportSourceLift l E g c d hSource).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  have := finiteExtension_completedPull_linear d g
  have := finiteExtension_open_linear d c.i c.isOpenImmersion
  have := finiteExtension_push_linear d c.g
  have : (cbcCompactSupportSource g c d).Linear
      (Padic.coefficientExtensionIntegers l E) := by
    unfold cbcCompactSupportSource
    infer_instance
  constructor
  intro M N f a
  apply ObjectProperty.hom_ext
  exact Functor.map_smul (cbcCompactSupportSource g c d) a f.hom

/-- The target restriction respects the actual constant-section scalar action.
Proof: tensor, pullback and direct image commute with scalar multiples of maps on
representatives. These equations survive localization and full-subcategory restriction.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportTargetLift_linear
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    (cbcCompactSupportTargetLift l E g' c' d hTarget).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  have := finiteExtension_completedPull_linear d g'
  have := finiteExtension_open_linear d c'.i c'.isOpenImmersion
  have := finiteExtension_push_linear d c'.g
  have : (cbcCompactSupportTarget g' c' d).Linear
      (Padic.coefficientExtensionIntegers l E) := by
    unfold cbcCompactSupportTarget
    infer_instance
  constructor
  intro M N f a
  apply ObjectProperty.hom_ext
  exact Functor.map_smul (cbcCompactSupportTarget g' c' d) a f.hom

/-- The two rational functors obtained by scalar transport of these lifts.
Source: `prop-weil-pbc-rational-transport`
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportSourceTransport
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :=
  ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
    (cbcCompactSupportSourceLift l E g c d hSource)

/-- The target rational functor obtained by scalar transport of the target lift.
Source: `prop-weil-pbc-rational-transport`
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportTargetTransport
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :=
  ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
    (cbcCompactSupportTargetLift l E g' c' d hTarget)

/-- The canonical scalar-localized component for one integral representative.
Source: the completed exchange in the compact-support square
(blueprint: thm-cbc-finite-extension). -/
def finiteExtensionCompactSupportExchangeComponent
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar) [QuasiCompact f]
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
    (hSource : ∀ K : PbcBoundedConstructibleComplete X
      (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
      (((pbcPadicCoefficientDatum l E).completedPull g).obj
        (((pbcPadicCoefficientDatum l E).push c.g).obj
          ((cbcDerivedOpenShriek (pbcPadicCoefficientDatum l E) c.i
            c.isOpenImmersion).obj K.obj))))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X
      (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
      (((pbcPadicCoefficientDatum l E).push c'.g).obj
        ((cbcDerivedOpenShriek (pbcPadicCoefficientDatum l E) c'.i
          c'.isOpenImmersion).obj
          (((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj))))
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E))
    (hComplete : cbcCompleteProperty (pbcPadicCoefficientDatum l E) X r a ha K.obj) :
    (cbcCompactSupportSourceTransport l E g c
      (pbcPadicCoefficientDatum l E) hSource).obj ⟨K⟩ ⟶
    (cbcCompactSupportTargetTransport l E g' c'
      (pbcPadicCoefficientDatum l E) hTarget).obj ⟨K⟩ :=
  (pbcRationalization Y' (pbcPadicCoefficientDatum l E)
    (Padic.coefficientExtensionUniformizer l E)).map
    (ObjectProperty.homMk
      (completedCompactSupportExchange (pbcPadicCoefficientDatum l E)
        c c' gbar properSquare openSquare r a ha ⟨K.obj, hComplete⟩))

attribute [local irreducible] cbcDerivedOpenShriek
  AdicCoefficientDatum.completedPull cbcOrdinaryExchange cbcCompletedPullbackComparison
  AdicCoefficientDatum.completedExchange cbcDatumCompletedTransport
  Functor.rightDerivedFunctor

attribute [local irreducible] ScalarLocalization.transport

/-- The category-domain hypotheses used by the identity and pasted-square clauses.
This only collects the three geometric conditions from the statement.
Source: blueprint thm-cbc-finite-extension, statement, first paragraph
(blueprint: thm-cbc-finite-extension). -/
def CbcFiniteExtensionDomain (l : ℕ) (T : Scheme.{u}) : Prop :=
  IsNoetherian T ∧ (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞)) ∧
    ∀ x : T, IsUnit (l : T.presheaf.stalk x)

/-- Intrinsic completeness of a selected integral object, for every presentation of I.
Source: blueprint thm-cbc-finite-extension, proof step 2
(blueprint: thm-cbc-finite-extension).
Proof: membership includes invertibility of the intrinsic Koszul completion unit on
some generating tuple and representative. The canonical coefficient comparison transports
that unit, retaining its normalization. Koszul reconstruction identifies it with the
canonical quotient-tower completion map. For any other finite tuple generating the same
ideal and any other representative, reconstruction identifies its unit with that same map,
conjugated by the representative comparison. Its invertibility is therefore unchanged.
Use the specified Q preimage representative to obtain cbcCompleteProperty. This also
covers the empty tuple when it generates the ideal; no completeness hypothesis is added. -/
theorem finiteExtension_cbcComplete
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E))
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal) :
    cbcCompleteProperty (pbcPadicCoefficientDatum l E) T r a ha K.obj := by
  exact wfConstructible_complete T (pbcPadicCoefficientDatum l E) r a ha K

/-- Localization of an ambient arrow between selected integral objects.
Applied to a path, this is its rational path: the full inclusion and localization preserve
composition and identities. In particular the following equations use the actual canonical
integral comparisons, with no arbitrary endpoint isomorphism.
Source: blueprint thm-cbc-finite-extension, proof steps 3 and 6
(blueprint: thm-cbc-finite-extension). -/
def finiteExtensionRationalArrow
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T : Scheme.{u}} {M N : (pbcPadicCoefficientDatum l E).derived T}
    (hM : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) M)
    (hN : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) N)
    (v : M ⟶ N) :
    (pbcRationalization T (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj ⟨M, hM⟩ ⟶
    (pbcRationalization T (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj ⟨N, hN⟩ :=
  (pbcRationalization T (pbcPadicCoefficientDatum l E)
    (Padic.coefficientExtensionUniformizer l E)).map (ObjectProperty.homMk v)

section Coherence

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end Coherence

end AlgebraicGeometry.Scheme
