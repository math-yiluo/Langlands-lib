/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
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
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.PerfectProjection.PerfectProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.Sites.MonObj

/-! # Integral quotient scalar comparison for unbounded direct image

Positive quotient levels are indexed by n + 1. All categories are ordinary unbounded
derived categories of the recorded internal module objects. No completion is applied.

## References

* Stacks Project, Tags 093M, 0D6D, 0D6E, 07A6 and 0944
* Stacks 06YY
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open MonoidalLeftAction
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded continuous integral condensed ring. -/
abbrev integral := (sfbCondensedIntegers l E).X

/-- Commutativity is inherited from the continuous-map ring sheaf. -/
instance integral_comm : IsCommMonObj (integral l E) := by
  let := spectralNorm.normedField (Padic l) E
  exact Profinite.isCommMonObj_continuousMapRingObjOfUniverse
    (Padic.coefficientExtensionIntegers l E)

/-- The discrete topology on the existing finite quotient, at exponent n + 1. -/
instance quotientTopology (n : ℕ) :
    TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥

/-- The finite quotient has its discrete topology. -/
instance quotientDiscrete (n : ℕ) :
    DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩

/-- A discrete ring is a topological ring. -/
instance quotientTopologicalRing (n : ℕ) :
    IsTopologicalRing (Padic.coefficientExtensionRing l E (n + 1)) :=
  inferInstance

/-- The discrete finite condensed quotient, using the existing continuous-map construction. -/
abbrev finite (n : ℕ) :=
  Profinite.continuousMapRingObjOfUniverse.{u, u}
    (Padic.coefficientExtensionRing l E (n + 1))

/-- The finite condensed ring has the recorded ring-sheaf monoid structure. -/
instance finiteMonObj (n : ℕ) : MonObj (finite l E n) :=
  Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse (Padic.coefficientExtensionRing l E (n + 1)))

/-- Commutativity is inherited from the finite quotient ring. -/
instance finite_comm (n : ℕ) : IsCommMonObj (finite l E n) :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse
    (Padic.coefficientExtensionRing l E (n + 1))

/-- Continuity of the actual quotient, rather than a choice of a finite projection. -/
theorem reduction_continuous (n : ℕ) :
    @Continuous _ _ (Padic.coefficientExtensionIntegersTopology l E)
      (quotientTopology l E n)
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
  let := spectralNorm.normedField (Padic l) E
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  exact (Padic.coefficientExtension_integers_coset_basis l E x).mem_of_mem
    (i := n) trivial

/-- The actual finite projection on condensed coefficients, induced by postcomposition. -/
def reduction (n : ℕ) : integral l E ⟶ finite l E n :=
  letI := spectralNorm.normedField (Padic l) E
  Profinite.continuousMapRingObjMapOfUniverse
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
    (reduction_continuous l E n)

/-- The finite projection is the underlying map of a morphism of ring sheaves. -/
instance reductionMonHom (n : ℕ) : IsMonHom (reduction l E n) := by
  let := spectralNorm.normedField (Padic l) E
  exact Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMapOfUniverse
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
      (reduction_continuous l E n))

/-- The scalar-extension functor in the quotient coefficient category. -/
def scalar (T : Scheme.{u}) (n : ℕ) :=
  (Mod.extendScalars (coefficientMap (reduction l E n) T)).leftDerivedFunctor

/-- Exact scalar restriction, descended termwise to the unbounded derived category. -/
def restrict (T : Scheme.{u}) (n : ℕ) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finite l E n) T)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (integral l E) T)) :=
  (Mod.comap (C := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap (reduction l E n) T)).mapDerivedCategory

/-- The specified derived extension/restriction adjunction. -/
def scalarAdjunction (T : Scheme.{u}) (n : ℕ) :
    scalar l E T n ⊣ restrict l E T n :=
  Mod.derivedExtendMapDerivedCategoryAdjunction _

end AlgebraicGeometry.ProEtale.IntegralQuotient

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual quotient transition for any two positive levels. -/
def transition (n m : ℕ) (h : m ≤ n) :
    Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l E (m + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The induced condensed quotient transition is postcomposition by the quotient factor. -/
def finiteMap (n m : ℕ) (h : m ≤ n) : finite l E n ⟶ finite l E m :=
  Profinite.continuousMapRingObjMapOfUniverse
    (transition l E n m h) continuous_of_discreteTopology

/-- The actual transition is a homomorphism of the specified coefficient ring objects. -/
instance finiteMapMonHom (n m : ℕ) (h : m ≤ n) :
    IsMonHom (finiteMap l E n m h) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMapOfUniverse
      (transition l E n m h) continuous_of_discreteTopology)

/-- Multiplication by the actual uniformizer power on continuous integral sections. -/
def multiplicationPoint (n : ℕ) : integral l E ⟶ integral l E := by
  letI := spectralNorm.normedField (Padic l) E
  refine ⟨{ app := fun S ↦ AddCommGrpCat.ofHom {
    toFun := fun x ↦ ULift.up
      ((ContinuousMap.const S.unop (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) *
        x.down)
    map_zero' := by
      apply ULift.ext
      exact mul_zero _
    map_add' := by
      intro x y
      apply ULift.ext
      exact mul_add _ _ _ }, naturality := ?_ }⟩
  intro S T g
  rfl

/-- Multiplication by the scalar power on the pulled-back ring sheaf. -/
def multiplicationHom (T : Scheme.{u}) (n : ℕ) :
    condensedRingObj (integral l E) T ⟶ condensedRingObj (integral l E) T :=
  (upperStarFromPoint T).map (multiplicationPoint l E n)

/-- The scalar multiplication map is linear for the regular module structure. -/
theorem multiplication_linear (T : Scheme.{u}) (n : ℕ) :
    γ[condensedRingObj (integral l E) T,
      (Mod.regular (condensedRingObj (integral l E) T)).X] ≫
        multiplicationHom l E T n =
      condensedRingObj (integral l E) T ◁ multiplicationHom l E T n ≫
        γ[condensedRingObj (integral l E) T,
      (Mod.regular (condensedRingObj (integral l E) T)).X] := by
  let := spectralNorm.normedField (Padic l) E
  have hp : MonObj.mul ≫ multiplicationPoint l E n =
      integral l E ◁ multiplicationPoint l E n ≫ MonObj.mul := by
    let : MonObj (integral l E).obj :=
      (Profinite.continuousMapRingSheafOfUniverse
        (Padic.coefficientExtensionIntegers l E)).obj.monObjCompForget₂
    apply Sheaf.tensor_hom_ext
    simp only [Functor.map_comp]
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
    have hR := Sheaf.μ_comp_map_mul (integral l E)
    simp only [reassoc_of% hR, hR]
    ext S : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    change Padic.coefficientExtensionUniformizer l E ^ (n + 1) *
        (a.down s * b.down s) =
      a.down s * (Padic.coefficientExtensionUniformizer l E ^ (n + 1) * b.down s)
    exact mul_left_comm _ _ _
  change (Functor.LaxMonoidal.μ (upperStarFromPoint T) _ _ ≫
      (upperStarFromPoint T).map MonObj.mul) ≫
        (upperStarFromPoint T).map (multiplicationPoint l E n) =
    _ ◁ (upperStarFromPoint T).map (multiplicationPoint l E n) ≫
      Functor.LaxMonoidal.μ (upperStarFromPoint T) _ _ ≫
        (upperStarFromPoint T).map MonObj.mul
  rw [Category.assoc, ← Functor.map_comp, hp, Functor.map_comp,
    ← Functor.LaxMonoidal.μ_natural_right_assoc]

/-- The linear endomorphism of the rank-one free module used in the displayed resolution. -/
def multiplication (T : Scheme.{u}) (n : ℕ) :
    Mod.regular (condensedRingObj (integral l E) T) ⟶
      Mod.regular (condensedRingObj (integral l E) T) :=
  Mod.Hom.mk' (multiplicationHom l E T n) (multiplication_linear l E T n)

/-- The cone of pi^(n+1) on the ring in degree zero, in degrees -1 and 0. -/
def resolution (T : Scheme.{u}) (n : ℕ) :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor _ 0).map
    (multiplication l E T n))

/-- The actual projection to the quotient is linear after scalar restriction. -/
theorem projection_linear (T : Scheme.{u}) (n : ℕ) :
    γ[condensedRingObj (integral l E) T,
      (Mod.regular (condensedRingObj (integral l E) T)).X] ≫
        coefficientMap (reduction l E n) T =
      condensedRingObj (integral l E) T ◁ coefficientMap (reduction l E n) T ≫
        γ[condensedRingObj (integral l E) T, ((Mod.comap (coefficientMap (reduction l E n) T)).obj
          (Mod.regular (condensedRingObj (finite l E n) T))).X] := by
  change MonObj.mul ≫ coefficientMap (reduction l E n) T =
    _ ◁ coefficientMap (reduction l E n) T ≫
      coefficientMap (reduction l E n) T ▷ _ ≫ MonObj.mul
  rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc]

/-- The augmentation in degree zero is the actual finite projection. -/
def projection (T : Scheme.{u}) (n : ℕ) :
    Mod.regular (condensedRingObj (integral l E) T) ⟶
      (Mod.comap (coefficientMap (reduction l E n) T)).obj
        (Mod.regular (condensedRingObj (finite l E n) T)) :=
  Mod.Hom.mk' (coefficientMap (reduction l E n) T) (projection_linear l E T n)

end AlgebraicGeometry.ProEtale.IntegralQuotient

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual finite projections commute with every quotient transition. -/
theorem reduction_comp (n m : ℕ) (h : m ≤ n) :
    reduction l E n ≫ finiteMap l E n m h = reduction l E m := by
  let := spectralNorm.normedField (Padic l) E
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext S
  ext x
  apply ULift.ext
  apply ContinuousMap.ext
  intro s
  rfl

end AlgebraicGeometry.ProEtale.IntegralQuotient
