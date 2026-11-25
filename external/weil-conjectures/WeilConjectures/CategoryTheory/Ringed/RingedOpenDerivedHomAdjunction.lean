/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedOpenDerivedTensorProjection
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.Integral.IntegralStratumProjectionInternalHom

/-! # Internal Hom out of extension from a ringed slice

Source: Stacks Project, Tags 0E8I and 06YN
(blueprint: lem-weil-pbc-ringed-open-derived-hom-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules WeilConjectures
namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{c, v, r} J R)]
  [HasDerivedCategory.{w}
    (RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U))]

-- The unbounded derived comparisons require elaborating several functor structures.
/-- For any right adjoint G of slice restriction, internal Hom out of a slice
extension is G of the internal Hom into the restricted argument.
Source: Stacks Project, Tags 0E8I and 06YN
(blueprint: lem-weil-pbc-ringed-open-derived-hom-adjunction).

Proof: the derived projection formula identifies tensor with the extension of P
with restriction, tensor with P, and extension in succession. Each of these three
functors has its specified right adjoint. Their composite right adjoint is
restriction followed by internal Hom from P followed by G. Uniqueness of right
adjoints identifies this with internal Hom from the extension of P. Naturality
in the variable argument is part of the uniqueness isomorphism. No boundedness
or compactness condition is used. -/
theorem ringedOpenDerived_homAdjunction :
    let F : RingedDerivedNative.Modules.{c, v, r} J R ⥤
        RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U) :=
      localizedSystemRestriction.{c, v, r} R U
    let E : RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U) ⥤
        RingedDerivedNative.Modules.{c, v, r} J R :=
      localizedSystemExtension.{c, v, r} R U
    letI : F.Additive := localizedSystemRestrictionAdditive.{c, v, r} R U
    letI : E.Additive := localizedSystemExtensionAdditive.{c, v, r} R U
    letI : PreservesFiniteLimits E := localizedSystemExtensionLimits.{c, v, r} R U
    letI : PreservesFiniteColimits E := localizedSystemExtensionColimits.{c, v, r} R U
    letI : PreservesFiniteLimits F := localizedSystemRestrictionLimits.{c, v, r} R U
    letI : PreservesFiniteColimits F := localizedSystemRestrictionColimits.{c, v, r} R U
    ∀ (G : RingedHomUniverses.D.{max c v, v, r, w} (J.over U) (R.over U) ⥤
        RingedHomUniverses.D.{c, v, r, w} J R)
      (_a : F.mapDerivedCategory ⊣ G)
      (P : RingedHomUniverses.D.{max c v, v, r, w} (J.over U) (R.over U)),
      Nonempty (RingedHomUniverses.hom.{c, v, r, w} J R
        (E.mapDerivedCategory.obj P) ≅ F.mapDerivedCategory ⋙
          RingedHomUniverses.hom.{max c v, v, r, w} (J.over U) (R.over U) P ⋙ G) := by
  let F₀ : RingedDerivedNative.Modules.{c, v, r} J R ⥤
      RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U) :=
    localizedSystemRestriction.{c, v, r} R U
  let E₀ : RingedDerivedNative.Modules.{max c v, v, r} (J.over U) (R.over U) ⥤
      RingedDerivedNative.Modules.{c, v, r} J R :=
    localizedSystemExtension.{c, v, r} R U
  let : F₀.Additive := localizedSystemRestrictionAdditive.{c, v, r} R U
  let : E₀.Additive := localizedSystemExtensionAdditive.{c, v, r} R U
  let : PreservesFiniteLimits E₀ := localizedSystemExtensionLimits.{c, v, r} R U
  let : PreservesFiniteColimits E₀ := localizedSystemExtensionColimits.{c, v, r} R U
  let : PreservesFiniteLimits F₀ := localizedSystemRestrictionLimits.{c, v, r} R U
  let : PreservesFiniteColimits F₀ := localizedSystemRestrictionColimits.{c, v, r} R U
  dsimp only
  intro G a P
  let E := E₀.mapDerivedCategory
  let F := F₀.mapDerivedCategory
  let a₀ : E₀ ⊣ F₀ := localizedSystemAdjunction.{c, v, r} R U
  let ad : E ⊣ F := a₀.mapExactDerivedCategory
  obtain ⟨⟨m, ac, ev⟩, hm, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{c, v, r, w} J R
  dsimp only [CoefficientClosedStructure.monoidal] at hm
  subst m
  obtain ⟨⟨mu, acu, evu⟩, hmu, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{max c v, v, r, w} (J.over U) (R.over U)
  dsimp only [CoefficientClosedStructure.monoidal] at hmu
  subst mu
  let S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, w} J R) :=
    ⟨RingedDerivedNative.monoidal.{c, v, r, w} J R, ac, ev⟩
  let SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, r, w} (J.over U) (R.over U)) :=
    ⟨RingedDerivedNative.monoidal.{max c v, v, r, w} (J.over U) (R.over U), acu, evu⟩
  obtain ⟨φ⟩ := ringedOpenDerived_tensorProjection.{c, v, r, w} J R U
  exact internalHom_of_tensorProjection S SU
    (RingedDerivedNative.symmetric.{c, v, r, w} J R)
    (RingedDerivedNative.symmetric.{max c v, v, r, w} (J.over U) (R.over U))
    E F F G ad a φ P

end CategoryTheory
