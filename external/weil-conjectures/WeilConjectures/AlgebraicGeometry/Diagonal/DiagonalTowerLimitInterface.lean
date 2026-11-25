/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit

/-! # Shared definitions for the completed diagonal limit

These are the existing completed endpoints, normalized comparison maps, and limit
specifications, extracted unchanged so their proof dependencies can be imported below
the final assembly theorem.

Source: blueprint diagonal tower limit, clauses 1 and 3
(blueprint: def-sfb-diagonal-limit-interface).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false

universe u v w a b c vc r
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

local instance (priority := 3000) diagonalHasLimit
    {A : Type a} [Category.{v} A] [h : HasLimitsOfShape ℕᵒᵖ A] (H : ℕᵒᵖ ⥤ A) :
    HasLimit H := h.has_limit H

attribute [local instance 2200] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify

/-- Additivity of this specific limit functor, from its binary-product preservation.
Source: blueprint clause 1 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalLimitAdditive (A : Type a) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- A total right derived functor with its universal unit and K-injective computation.
Source: blueprint clause 1, total derived functors on strict towers
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
structure DiagonalRightDerived
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] where
  R : DerivedCategory A ⥤ DerivedCategory B
  η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R
  universal : R.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (.up ℤ))
  computation : ∀ P : CochainComplex A ℤ, P.IsKInjective → IsIso (η.app P)
  [shift : R.CommShift ℤ]
  triangulated : R.IsTriangulated

attribute [instance] DiagonalRightDerived.shift

/-- The total derived limit, including its canonical projections to the derived levels.
The normalization is an equation on complexes and fixes the maps, not just their types.
Source: blueprint clauses 1 and 3, Stacks 0940
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
structure DiagonalRlim
    (A : Type a) [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] extends
    DiagonalRightDerived (lim : (ℕᵒᵖ ⥤ A) ⥤ A) where
  -- The shift structure is normalized by the specified full cochain unit.
  [unitShift : NatTrans.CommShift η ℤ]
  projection : ∀ n : ℕ,
    R ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
  normalization : ∀ (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ),
    η.app P ≫ (projection n).app (DerivedCategory.Q.obj P) ≫
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app P =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app P)

attribute [instance] DiagonalRlim.unitShift

/-- Scalar forgetting preserves tower limits by the existing scalar adjunction.
Source: blueprint clause 1 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalForgetTowerLimits (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (diagonalForget ℓ X) :=
  (diagonalScalarAdjunction ℓ X).rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- Modules over the existing completed coefficient sheaf.
Source: blueprint completed coefficient convention, clause 3
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev DiagonalCompleted (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :=
  SheafOfModules.{u + 1} (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X ℓ))

/-- The existing abelian structure on completed coefficient modules, named once so
all derived expressions share its sheafification witnesses.
Source: blueprint completed coefficient convention, clause 3
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance (priority := 2000) diagonalCompletedAbelian
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) : Abelian (DiagonalCompleted ℓ X) :=
  inferInstance

local instance (priority := 3500) diagonalModLimits (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) : HasLimitsOfShape ℕᵒᵖ (DiagonalMod ℓ X) := inferInstance

local instance (priority := 3500) diagonalAbLimits (X : Scheme.{u}) :
    HasLimitsOfShape ℕᵒᵖ (DiagonalAb X) := inferInstance

local instance (priority := 3500) diagonalRingLimits (X : Scheme.{u}) :
    HasLimitsOfShape ℕᵒᵖ (Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) := inferInstance

local instance (priority := 3500) diagonalCompleteLimits (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) : HasLimitsOfShape ℕᵒᵖ (DiagonalCompleted ℓ X) := inferInstance

/-- The n-th component of the canonical completed coefficient pullback map.
Source: blueprint clause 1, completed source coefficients
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalCompletedCoefficientComponent (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (Scheme.purTwistZlCompletion Y ℓ) ⟶ Scheme.purTwistFiniteRing X ℓ n :=
  (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (Scheme.purTwistZlProjection Y ℓ n) ≫
    Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The finite components respect the prescribed quotient transitions.
Source: blueprint clause 1 (blueprint: proposition-ell-adic-cycle-class-diagonal).
Proof: the limit projections commute with every tower arrow. The constant-sheaf
inverse-image comparison is natural in a ring homomorphism, because it is adjoint
to the constant-section map. Apply this naturality to each quotient transition;
functoriality of inverse image then gives the displayed cone equation. -/
theorem diagonalCompletedCoefficient_naturality (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) {b a : ℕᵒᵖ} (g : b ⟶ a) :
    diagonalCompletedCoefficientComponent ℓ f b.unop ≫
      (Scheme.purTwistZlTower X ℓ).map g =
        diagonalCompletedCoefficientComponent ℓ f a.unop := by
  let : HasWeakSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    (AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X).isRightAdjoint
  let : HasWeakSheafify (Scheme.ProEt.topology Y) CommRingCat.{u + 1} :=
    (AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify Y).isRightAdjoint
  let F := Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let e : Scheme.purTwistZlTower Y ℓ ⋙ F ⟶ Scheme.purTwistZlTower X ℓ :=
    NatTrans.ofOpSequence
      (fun n ↦ Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))) (by
          intro n
          simp only [Functor.comp_map, Scheme.purTwistZlTower,
            Scheme.purTwistZlTowerOfUniverses, Functor.ofOpSequence_map_homOfLE_succ]
          exact Scheme.proEtaleConstantInverseImageMap_naturality f _)
  change (F.map (limit.π (Scheme.purTwistZlTower Y ℓ) b) ≫ e.app b) ≫
    (Scheme.purTwistZlTower X ℓ).map g =
      F.map (limit.π (Scheme.purTwistZlTower Y ℓ) a) ≫ e.app a
  rw [Category.assoc, ← e.naturality, ← Category.assoc, Functor.comp_map, ← F.map_comp, limit.w]

/-- The canonical map from inverse-image to completed coefficients on the source.
Its actual data is the limit lift of the finite constant-section comparisons.
Source: blueprint clause 1 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalCompletedCoefficientMap (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion Y ℓ) ⟶ Scheme.purTwistZlCompletion X ℓ :=
  limit.lift (Scheme.purTwistZlTower X ℓ)
    { pt := (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (Scheme.purTwistZlCompletion Y ℓ)
      π := { app n := diagonalCompletedCoefficientComponent ℓ f n.unop
             naturality _ _ g := (Category.id_comp _).trans
               (diagonalCompletedCoefficient_naturality ℓ f g).symm } }

/-- The supported completed constant with its canonical completed-coefficient action.
Use the completed coefficient sheaf on the diagonal, restricted along the actual
coefficient structure map before ringed direct image.
Source: blueprint Delta_* Z_l in clauses 1 and 3
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalCompletedSource (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) :
    DiagonalCompleted ℓ (diagonalSurface Y) :=
  (Scheme.proEtaleRingedDirectImage (diagonalImmersion Y)
    (Scheme.purTwistZlCompletion (diagonalSurface Y) ℓ)).obj
      ((SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (diagonalCompletedCoefficientMap ℓ (diagonalImmersion Y)))).obj
              (SheafOfModules.unit
                (Scheme.purTwistRing (ProjectiveLine Y)
                  (Scheme.purTwistZlCompletion (ProjectiveLine Y) ℓ))))

/-- Restrict the completed action to constant scalars, then to constant sections.
The two constant-ring presentations are identified by constantCommuteCompose.
Source: blueprint clause 3 and Stacks 099I
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalCompletedRestriction (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    DiagonalCompleted ℓ X ⥤ DiagonalMod ℓ X :=
  letI := Scheme.purTwistForgetPreservesSheafification X
  SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (Scheme.purTwistZlCompletionMap X ℓ)) ⋙
  SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).inv ⋙
  constantRingModuleRestriction.{u + 1, u} (Scheme.ProEt.topology X) (ULift.{u + 1} ℤ_[ℓ])

private theorem diagonalRestrictScalarsExact
    {C : Type a} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{b}] [J.WEqualsLocallyBijective AddCommGrpCat.{b}]
    {R S : Sheaf J RingCat.{b}} (r : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{b} r) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{b} r) := by
  let F := SheafOfModules.restrictScalars.{b} r
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{b} R) :=
    (moduleSheaves_colimits_forgetful R).2.2.1
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{b} S) :=
    (moduleSheaves_colimits_forgetful S).2.2.1
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{b} R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{b} S))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{b} R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{b} S))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{b} R) := inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{b} R),
    preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{b} R)⟩

/-- Constant-scalar restriction is additive and exact.
Source: blueprint clause 3, coefficient comparison (blueprint:
proposition-ell-adic-cycle-class-diagonal). Proof: all three factors retain the underlying additive
sheaf. Kernels are sectionwise and cokernels are additive sheafifications, so finite limits, finite
colimits and sums of morphisms are unchanged. The constant-ring equivalence extends the scalar
action uniquely by local gluing (lem-cbc-constant-ring-module-sheaves). -/
theorem diagonalCompletedRestriction_exact (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    (diagonalCompletedRestriction ℓ X).Additive ∧
    PreservesFiniteLimits (diagonalCompletedRestriction ℓ X) ∧
    PreservesFiniteColimits (diagonalCompletedRestriction ℓ X) := by
  obtain ⟨e, he, hAdd, _⟩ := (constant_ring_module_sheaves
    (Scheme.ProEt.topology X) (ULift.{u + 1} ℤ_[ℓ])).1
  have : (constantRingModuleRestriction (Scheme.ProEt.topology X)
      (ULift.{u + 1} ℤ_[ℓ])).Additive := he ▸ hAdd
  have : PreservesFiniteLimits (constantRingModuleRestriction
      (Scheme.ProEt.topology X) (ULift.{u + 1} ℤ_[ℓ])) :=
    he ▸ inferInstanceAs (PreservesFiniteLimits e.functor)
  have : PreservesFiniteColimits (constantRingModuleRestriction
      (Scheme.ProEt.topology X) (ULift.{u + 1} ℤ_[ℓ])) :=
    he ▸ inferInstanceAs (PreservesFiniteColimits e.functor)
  let := Scheme.purTwistForgetPreservesSheafification X
  have h₁ := diagonalRestrictScalarsExact
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (Scheme.purTwistZlCompletionMap X ℓ))
  have h₂ := diagonalRestrictScalarsExact
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).inv
  have := h₁.1
  have := h₁.2
  have := h₂.1
  have := h₂.2
  dsimp only [diagonalCompletedRestriction]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The additive part of coefficient restriction. Source: blueprint clause 3
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalCompletedRestrictionAdditive (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    (diagonalCompletedRestriction ℓ X).Additive :=
  (diagonalCompletedRestriction_exact ℓ X).1

/-- The left exact part of coefficient restriction. Source: blueprint clause 3
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalCompletedRestrictionLimits (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    PreservesFiniteLimits (diagonalCompletedRestriction ℓ X) :=
  (diagonalCompletedRestriction_exact ℓ X).2.1

/-- The right exact part of coefficient restriction. Source: blueprint clause 3
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalCompletedRestrictionColimits (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    PreservesFiniteColimits (diagonalCompletedRestriction ℓ X) :=
  (diagonalCompletedRestriction_exact ℓ X).2.2

/-- Simultaneous derived quotient with its canonical quotient units on arbitrary inputs.
The normalization with the left-derived counit specifies the actual quotient map.
Source: blueprint clause 3, derived finite reductions; Stacks 099M
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
structure DiagonalCompletedReductionData
    (ℓ : ℕ) (A : Type a) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] where
  derived : DiagonalDerivedReduction ℓ (𝟭 A)
  unit : ∀ n : ℕ, 𝟭 (DerivedCategory A) ⟶
    derived.T ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
  normalization : ∀ (P : CochainComplex A ℤ) (n : ℕ),
    (unit n).app (DerivedCategory.Q.obj P) ≫
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map
        (derived.ε.app P) ≫
      ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app
        ((derived.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (derived.ordinary.π n) (.up ℤ)).app P)

/-- The generic quotient interface at the completed coefficient category.
Source: blueprint finite quotient normalization
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev DiagonalCompletedReduction (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ X)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ X)] :=
  DiagonalCompletedReductionData ℓ (DiagonalCompleted ℓ X)

/-- The degree-zero supported completed coefficient object.
Source: blueprint clauses 1 and 3 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev diagonalCompletedDomain (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ (diagonalSurface Y))] :
    DerivedCategory.{w} (DiagonalCompleted ℓ (diagonalSurface Y)) :=
  (DerivedCategory.singleFunctor _ 0).obj (diagonalCompletedSource ℓ Y)

/-- The published completed Tate line shifted by two.
Source: blueprint clause 3 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev diagonalCompletedCodomain (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ (diagonalSurface Y))] :
    DerivedCategory.{w} (DiagonalCompleted ℓ (diagonalSurface Y)) :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (Scheme.purTwistZlModule (diagonalSurface Y) ℓ))⟦(2 : ℤ)⟧

/-- Exact derived restriction from completed to constant coefficients.
Source: blueprint clause 3 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev diagonalCompletedUnderlying (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{w} (DiagonalCompleted ℓ X)]
    [HasDerivedCategory.{w} (DiagonalMod ℓ X)] :=
  (diagonalCompletedRestriction ℓ X).mapDerivedCategory

/-- The ordinary limit cone maps to its total derived limit through the derived unit.
This is the canonical comparison with zero nullhomotopy on the Roos model.
Source: blueprint clause 1 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalOrdinaryRlim
    {A : Type a} [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) (H : ℕᵒᵖ ⥤ A) :
    (DerivedCategory.singleFunctor A 0).obj (limit H) ⟶
      L.R.obj ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj H) :=
  (DerivedCategory.singleFunctorIsoCompQ A 0).hom.app (limit H) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A) (.up ℤ) 0).inv.app H) ≫
    L.η.app ((HomologicalComplex.single (ℕᵒᵖ ⥤ A) (.up ℤ) 0).obj H) ≫
    L.R.map ((DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ A) 0).inv.app H)

attribute [local irreducible] diagonalOrdinaryRlim

/-- The supported integral constant has a unique coefficient-unit map into the
supported completed constant. On every constant integer section it is n times one.
Source: blueprint clauses 1 and 3, completed source convention
(blueprint: proposition-ell-adic-cycle-class-diagonal).
Proof: on the diagonal site send an integer n to n times one in the diagonal
completed ring. Ring restrictions preserve one and integer multiples, so these maps
form a presheaf morphism. The sheafification adjunction extends it uniquely from
the constant presheaf. Apply direct image along the diagonal. Every section of the
constant sheaf is locally a constant integer, so the displayed equations determine
the resulting additive sheaf map uniquely. -/
theorem diagonalCompletedGenerator_existsUnique (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) :
    ∃! γ : diagonalIntegralSource Y ⟶
        (diagonalForget ℓ (diagonalSurface Y)).obj
          ((diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
            (diagonalCompletedSource ℓ Y)),
      ∀ (U : (diagonalSurface Y).ProEtᵒᵖ) (n : ℤ),
        HEq (γ.hom.app U
          ((toSheafify (Scheme.ProEt.topology (ProjectiveLine Y))
            ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                (op ((Scheme.proEtaleBaseChange (diagonalImmersion Y)).obj U.unop))
                  (ULift.up n)))
          (n • (1 : (Scheme.purTwistZlCompletion (ProjectiveLine Y) ℓ).obj.obj
            (op ((Scheme.proEtaleBaseChange (diagonalImmersion Y)).obj U.unop)))) := by
  classical
  let Z := ProjectiveLine Y
  let J := Scheme.ProEt.topology Z
  let R := Scheme.purTwistZlCompletion Z ℓ
  let Q : Sheaf J AddCommGrpCat.{u + 1} :=
    (SheafOfModules.toSheaf (Scheme.purTwistRing Z R)).obj
      (SheafOfModules.unit (Scheme.purTwistRing Z R))
  let P := (Functor.const Z.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let t : P ⟶ Q.obj :=
    { app V := AddCommGrpCat.ofHom
        ((Int.castAddHom (R.obj.obj V)).comp AddEquiv.ulift.toAddMonoidHom)
      naturality := by
        intro V W f
        ext n
        exact (map_intCast (R.obj.map f).hom n.down).symm }
  let g : (constantSheaf J AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ Q :=
    ⟨sheafifyLift J t Q.property⟩
  have hg (V : Z.ProEtᵒᵖ) (n : ℤ) :
      g.hom.app V ((toSheafify J P).app V (ULift.up n)) =
        n • (1 : R.obj.obj V) := by
    change ((toSheafify J P ≫ sheafifyLift J t Q.property).app V) (ULift.up n) = _
    rw [toSheafify_sheafifyLift]
    change (n : R.obj.obj V) = n • (1 : R.obj.obj V)
    exact (zsmul_one n).symm
  let i := diagonalImmersion Y
  let F := lowerStar AddCommGrpCat.{u + 1} i
  have : IsIso (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).counit :=
    abelian_closed_counit i
  let ff := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).fullyFaithfulROfIsIsoCounit
  refine ⟨F.map g, ?_, ?_⟩
  · intro U n
    exact heq_of_eq (hg _ n)
  · intro γ hγ
    let g' := ff.preimage (X := (constantSheaf J AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (Y := Q) γ
    have hpre : F.map g' = γ := ff.map_preimage (X := (constantSheaf J AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (Y := Q) γ
    have hgg : g' = g := by
      let T := ⊤_ (diagonalSurface Y).ProEt
      let hT := terminalIsTerminal.isTerminalObj (Scheme.proEtaleBaseChange i) T
      apply ((constantSheafAdj J AddCommGrpCat.{u + 1} hT).homEquiv _ Q).injective
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      ext n
      obtain ⟨n⟩ := n
      change g'.hom.app (op ((Scheme.proEtaleBaseChange i).obj T))
        ((toSheafify J P).app _ (ULift.up n)) =
        g.hom.app (op ((Scheme.proEtaleBaseChange i).obj T))
          ((toSheafify J P).app _ (ULift.up n))
      rw [hg]
      have h := eq_of_heq (hγ (op T) n)
      rw [← hpre] at h
      exact h
    rw [← hpre, hgg]

/-- The unique coefficient-unit map, determined on locally constant integers.
Source: blueprint completed source convention
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalCompletedGenerator (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) :=
  (diagonalCompletedGenerator_existsUnique ℓ Y).exists.choose

attribute [local irreducible] diagonalCompletedSource
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Assemble the degree-zero comparison using an exact functor and an ordinary limit. -/
def diagonalSingleLimitComparison
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DiagonalRlim B) (P : A) (H : ℕᵒᵖ ⥤ B) (K : DerivedCategory (ℕᵒᵖ ⥤ B))
    (s : F.obj P ≅ limit H) (a : K ≅ (DerivedCategory.singleFunctor _ 0).obj H) :
    F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj P) ⟶ L.R.obj K :=
  (F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
    (DerivedCategory.singleFunctor _ 0).map s.hom ≫ diagonalOrdinaryRlim L H ≫ L.R.map a.inv

/-- Assemble the shifted comparison using an exact functor and an ordinary limit. -/
def diagonalShiftedSingleLimitComparison
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DiagonalRlim B) (P : A) (H : ℕᵒᵖ ⥤ B) (K : DerivedCategory (ℕᵒᵖ ⥤ B))
    (s : F.obj P ≅ limit H) (a : K ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor _ 0).obj P)⟦(2 : ℤ)⟧) ⟶
      L.R.obj K :=
  (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj P) ≫
    (shiftFunctor _ (2 : ℤ)).map
      ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
        (DerivedCategory.singleFunctor _ 0).map s.hom ≫ diagonalOrdinaryRlim L H) ≫
    (L.R.commShiftIso (2 : ℤ)).inv.app ((DerivedCategory.singleFunctor _ 0).obj H) ≫
    L.R.map a.inv

/-- The source endpoint identification induced by the ordinary limit comparison
and the already normalized derived source counit.
Source: blueprint clauses 1 and 3 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalSourceLimitMap (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (s : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (diagonalCompletedSource ℓ Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y))) :
    (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj (diagonalCompletedDomain ℓ Y) ⟶
      L.R.obj (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))) :=
  diagonalSingleLimitComparison (diagonalCompletedRestriction ℓ (diagonalSurface Y)) L
    (diagonalCompletedSource ℓ Y) _ _ s a

attribute [local irreducible] diagonalSourceLimitMap

/-- The target endpoint identification induced by the ordinary root limit,
the canonical shift comparison, and the existing signed Kummer identification.
Source: blueprint clauses 1 and 3 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalTargetLimitMap (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
    (t : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H) :
    (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj (diagonalCompletedCodomain ℓ Y) ⟶
      L.R.obj (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
        (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)) :=
  diagonalShiftedSingleLimitComparison (diagonalCompletedRestriction ℓ (diagonalSurface Y)) L
    (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) _ _ t b

attribute [local irreducible] diagonalTargetLimitMap

/-- Exact functoriality of Ext with the categorical interfaces shared by name.
Source: exact functoriality of derived categories
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalExactFunctorExtImage
    {A : Type a} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {B : Type b} [Category.{u} B] [Abelian B] [HasExt.{w} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S U : A} {n : ℕ} (δ : Ext S U n) : Ext (F.obj S) (F.obj U) n :=
  δ.mapExactFunctor F

attribute [local irreducible] diagonalSingleLimitComparison diagonalExactFunctorExtImage
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The root-limit comparison with its two diagrams fixed before composing isomorphisms.
Source: blueprint root limit normalization (blueprint:
proposition-ell-adic-cycle-class-diagonal). -/
def diagonalRootLimitComparison (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (H : DiagonalSystems ℓ X)
    (roots : H ⋙ diagonalForget ℓ X ≅
      Scheme.proEtaleRootsOfUnityTower X ℓ (Fact.out : ℓ.Prime)) :
    (diagonalForget ℓ X).obj (limit H) ≅
      limit (Scheme.proEtaleRootsOfUnityTower X ℓ (Fact.out : ℓ.Prime)) :=
  (preservesLimitIso (diagonalForget ℓ X) H).trans
    (HasLimit.isoOfNatIso (F := H ⋙ diagonalForget ℓ X)
      (G := Scheme.proEtaleRootsOfUnityTower X ℓ (Fact.out : ℓ.Prime)) roots)

/-- Finite evaluations of a strict-system Ext class with fixed normalizations.
Source: blueprint finite quotient normalization
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalFiniteCycleNormalization
    {A : Type a} [Category.{v} A] [Abelian A]
    [HasExt.{w} A] [HasExt.{w} (ℕᵒᵖ ⥤ A)]
    (S H : ℕᵒᵖ ⥤ A) (c : Ext.{w} S H 2)
    (P Q : ℕ → A)
    (sourceNorm : ∀ n : ℕ, (S.obj (op n) ≅ P n) → Prop)
    (targetNorm : ∀ n : ℕ, (H.obj (op n) ≅ Q n) → Prop)
    (finiteClass : ∀ n : ℕ, Ext.{w} (P n) (Q n) 2) : Prop :=
  ∀ n : ℕ, ∃ (s : S.obj (op n) ≅ P n) (t : H.obj (op n) ≅ Q n),
    sourceNorm n s ∧ targetNorm n t ∧
      (Ext.mk₀.{w} s.inv).comp
        ((c.mapExactFunctor ((evaluation ℕᵒᵖ A).obj (op n))).comp
          (Ext.mk₀.{w} t.hom) (add_zero 2)) (zero_add 2) = finiteClass n

/-- Compatibility of an arrow with completion and all finite quotient units.
Source: blueprint clause 3 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def DiagonalArrowCompatibility
    {C : Type a} [Category.{v} C] [Preadditive C]
    {B : Type b} [Category.{u} B] [Preadditive B]
    {E : Type w} [Category.{v} E]
    (ℓ : ℕ) (F : C ⥤ B) (R : E ⥤ B)
    (Rn : ℕ → C ⥤ C) (En : ℕ → E ⥤ B)
    (unit : ∀ n, 𝟭 C ⟶ Rn n) (π : ∀ n, R ⟶ En n)
    (P Q : C) (K J : E) (f : K ⟶ J)
    (s : F.obj P ⟶ R.obj K) (t : F.obj Q ⟶ R.obj J) : Prop :=
  IsIso s ∧ IsIso t ∧
    (∀ V : C, IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ P)) ∧
    (∀ V : C, IsIso (ℓ • 𝟙 V) → Subsingleton (V ⟶ Q)) ∧
    (∃! δ : P ⟶ Q, F.map δ ≫ t = s ≫ R.map f) ∧
    ∀ δ : P ⟶ Q, F.map δ ≫ t = s ≫ R.map f → ∀ n : ℕ,
      ∃ (a : F.obj ((Rn n).obj P) ≅ (En n).obj K)
        (b : F.obj ((Rn n).obj Q) ≅ (En n).obj J),
        F.map ((unit n).app P) ≫ a.hom = s ≫ (π n).app K ∧
        F.map ((unit n).app Q) ≫ b.hom = t ≫ (π n).app J ∧
        F.map ((Rn n).map δ) = a.hom ≫ (En n).map f ≫ b.inv

/-- The completed coefficient clause using the shared exact functor and endpoint maps.
Source: blueprint diagonal limit clause 3 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalCompleteDataAssertion
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category.{u} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ B]
    (ℓ : ℕ) (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P Q : A) (S H : ℕᵒᵖ ⥤ B) (K J : DerivedCategory (ℕᵒᵖ ⥤ B))
    (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor _ 0).obj S)
    (b : J ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (sourceNorm : (F.obj P ≅ limit S) → Prop)
    (targetNorm : (F.obj Q ≅ limit H) → Prop) : Prop :=
  ∃ (L : DiagonalRlim B) (M : DiagonalCompletedReductionData ℓ A)
    (s : F.obj P ≅ limit S) (t : F.obj Q ≅ limit H),
    sourceNorm s ∧ targetNorm t ∧
    DiagonalArrowCompatibility ℓ F.mapDerivedCategory L.R
      (fun n ↦ M.derived.T ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory)
      (fun n ↦ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory)
      M.unit L.projection ((DerivedCategory.singleFunctor _ 0).obj P)
      (((DerivedCategory.singleFunctor _ 0).obj Q)⟦(2 : ℤ)⟧) K J f
      (diagonalSingleLimitComparison F L P S K s a)
      (diagonalShiftedSingleLimitComparison F L Q H J t b)

/-- The simultaneous finite and completed normalization for an integral boundary.
Source: blueprint diagonal tower limit, clauses 1 and 3
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def DiagonalLimitDataSpec
    (ℓ : ℕ) {A : Type a} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    {B : Type b} [Category.{u} B] [Abelian B]
    {C : Type c} [Category.{vc} C] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ C)] [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ B]
    (L₀ : A ⥤ B) (D : DiagonalDerivedReduction ℓ L₀)
    (S U : A) (boundary : Ext S U 1)
    (F : C ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P Q : C) (root : (ℕᵒᵖ ⥤ B) → Type r)
    (finite : ∀ H : ℕᵒᵖ ⥤ B, root H → Ext (D.ordinary.E.obj S) H 2 → Prop)
    (sourceNorm : (F.obj P ≅ limit (D.ordinary.E.obj S)) → Prop)
    (targetNorm : ∀ H : ℕᵒᵖ ⥤ B, root H → (F.obj Q ≅ limit H) → Prop) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : root H)
    (a : D.T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S))
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj U)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj S) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ L₀ D S ∧
      c.hom = a.inv ≫ D.T.map boundary.hom ≫ b.hom ∧ finite H roots c ∧
      diagonalCompleteDataAssertion ℓ F P Q (D.ordinary.E.obj S) H _ _
        (D.T.map boundary.hom) a b sourceNorm (targetNorm H roots)

attribute [local irreducible] diagonalRootLimitComparison
  diagonalFiniteCycleNormalization DiagonalArrowCompatibility
  diagonalCompleteDataAssertion DiagonalLimitDataSpec

attribute [local instance 5000] hasExt_of_enoughInjectives

end AlgebraicGeometry.ProEtale
