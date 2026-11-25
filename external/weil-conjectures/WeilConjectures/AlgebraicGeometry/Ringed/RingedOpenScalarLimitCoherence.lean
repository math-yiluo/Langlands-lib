/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProducts
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Basic.Denumerable
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
public import WeilConjectures.CategoryTheory.NormalizedLimitSquare.NormalizedLimitSquareCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import Mathlib.CategoryTheory.Adjunction.Whiskering

import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
/-!
# Scalar and normalized inverse-limit coherence for ringed open extension

## Main statements

- `ringedOpenScalarLimitCoherence`: canonical scalar/open and normalized-limit coherence.
- `CbcLimitNormalized`: the specified ordinary-limit and K-injective normalization.
- `CbcAugmentationCompatible`: compatibility with all strict augmentation maps.

## References

* Stacks Project, Tags 09BP, 03DI, 03DJ and 03CY
* Stacks 05RU
* Stacks 0941
* Stacks 03DI, the two explicit Hom maps
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u vA uA vB uB vC uC vD uD wA wB wC wD

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
attribute [-instance] RingedOpenScalar.scalarLimits RingedOpenScalar.scalarColimits
  RingedOpenScalar.sliceLimits RingedOpenScalar.sliceColimits

namespace CategoryTheory

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimits A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Actual derived postcomposition on strict towers, with levelwise exactness. -/
abbrev cbcTowerDerived : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤
    DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The actual complex-to-derived factorization for tower postcomposition. -/
abbrev cbcTowerFactors :=
  @Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The ordinary-limit unit normalization of the specified comparison. This is the
K-injective normalization of `exactProductFunctorStrictLimit`: on a K-injective tower
it reads `F lim I → lim FI → Rlim FI`. Its Roos description is precisely that theorem's
signed two-summand formula, not an unspecified triangle isomorphism. -/
structure CbcLimitNormalized
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (lambda : LA ⋙ F.mapDerivedCategory ≅ cbcTowerDerived F ⋙ LB) : Prop where
  equation : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (etaA.app X) ≫ lambda.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((cbcTowerFactors F).hom.app X) =
      F.mapDerivedCategoryFactors.hom.app (limit X.asFunctor) ≫
        DerivedCategory.Q.map
          (limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone (limit.cone X.asFunctor))) ≫
        etaB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj X)

end

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]

/-- Canonical localization of a commuting square, using the existing derived composition
and natural-isomorphism transports, including their exact complex factorizations. -/
def cbcDerivedSquare (e : F ⋙ G ≅ H ⋙ K) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso e

/-- The same canonical square on derived strict towers, using levelwise exactness. -/
def cbcDerivedTowerSquare
    [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory.{wC} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wD} (ℕᵒᵖ ⥤ D)]
    (e : F ⋙ G ≅ H ⋙ K) :
    cbcTowerDerived F ⋙ cbcTowerDerived G ≅ cbcTowerDerived H ⋙ cbcTowerDerived K :=
  CategoryTheory.NormalizedLimitSquare.towerSquare F G H K e

end

/-- Unit and counit equations for the scalar/open-extension square. -/
def CbcAdjunctionCompatible
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
    {qS : C ⥤ A} {qR : D ⥤ B}
    (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
    (adjS : JS ⊣ qS) (adjR : JR ⊣ qR) : Prop :=
  (∀ N : A, rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) ≫
    qR.map (e.hom.app N) = adjR.unit.app (rU.obj N)) ∧
  (∀ Q : C, e.hom.app (qS.obj Q) ≫ JR.map (d.inv.app Q) ≫
    adjR.counit.app (rT.obj Q) = rT.map (adjS.counit.app Q))

/-- Canonical square on complexes with its composition factors explicit. -/
def cbcComplexSquare
    {A : Type uA} [Category.{vA} A] [Preadditive A]
    {B : Type uB} [Category.{vB} B] [Preadditive B]
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ K.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ)

section EquationCalculus

variable {A B C D : Type uA} [Category.{vA} A] [Category.{vA} B]
  [Category.{vA} C] [Category.{vA} D]
  {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
  {qS : C ⥤ A} {qR : D ⥤ B}
  (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
  (adjS : JS ⊣ qS) (adjR : JR ⊣ qR)

private theorem inverseMate_of_unit
    (hu : ∀ N : A, rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) ≫
      qR.map (e.hom.app N) = adjR.unit.app (rU.obj N)) :
    ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans = e.inv := by
  ext N
  apply (adjR.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change adjR.unit.app (rU.obj N) ≫ qR.map
      (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans.app N) = _
  have h := unit_mateEquiv_symm adjS adjR (TwoSquare.mk _ _ _ _ d.inv) N
  change rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) =
    adjR.unit.app (rU.obj N) ≫ qR.map
      (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans.app N) at h
  rw [← h, ← hu N]
  simp only [Category.assoc]
  rw [← qR.map_comp, Iso.hom_inv_id_app]
  erw [qR.map_id]
  erw [Category.comp_id]

private theorem equations_of_inverseMate
    (hm : ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans = e.inv) :
    CbcAdjunctionCompatible e d adjS adjR := by
  have hu (N : A) := unit_mateEquiv_symm adjS adjR (TwoSquare.mk _ _ _ _ d.inv) N
  have hc (Q : C) := mateEquiv_counit_symm adjS adjR (TwoSquare.mk _ _ _ _ d.inv) Q
  constructor
  · intro N
    have hu' := hu N
    change rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) =
      adjR.unit.app (rU.obj N) ≫ qR.map
        (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans.app N) at hu'
    rw [hm] at hu'
    rw [reassoc_of% hu']
    rw [← qR.map_comp, Iso.inv_hom_id_app]
    erw [qR.map_id]
    rw [Category.comp_id]
  · intro Q
    have hc' := hc Q
    change JR.map (d.inv.app Q) ≫ adjR.counit.app (rT.obj Q) =
      (((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans.app (qS.obj Q)) ≫
        rT.map (adjS.counit.app Q) at hc'
    rw [hm] at hc'
    rw [hc', Iso.hom_inv_id_app_assoc]

variable [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive]

private theorem equations_complex (he : CbcAdjunctionCompatible e d adjS adjR) :
    CbcAdjunctionCompatible
      (JS := JS.mapHomologicalComplex (.up ℤ))
      (JR := JR.mapHomologicalComplex (.up ℤ))
      (rU := rU.mapHomologicalComplex (.up ℤ))
      (rT := rT.mapHomologicalComplex (.up ℤ))
      (qS := qS.mapHomologicalComplex (.up ℤ))
      (qR := qR.mapHomologicalComplex (.up ℤ))
      (cbcComplexSquare JS rT rU JR e)
      (cbcComplexSquare rT qR qS rU d)
      (adjS.mapHomologicalComplex (.up ℤ)) (adjR.mapHomologicalComplex (.up ℤ)) := by
  unfold cbcComplexSquare
  constructor
  · intro N
    apply HomologicalComplex.Hom.ext
    funext i
    exact he.1 (N.X i)
  · intro Q
    apply HomologicalComplex.Hom.ext
    funext i
    exact he.2 (Q.X i)

omit [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive] in
private theorem equations_tower (he : CbcAdjunctionCompatible e d adjS adjR) :
    CbcAdjunctionCompatible
      (JS := (Functor.whiskeringRight ℕᵒᵖ A C).obj JS)
      (JR := (Functor.whiskeringRight ℕᵒᵖ B D).obj JR)
      (rU := (Functor.whiskeringRight ℕᵒᵖ A B).obj rU)
      (rT := (Functor.whiskeringRight ℕᵒᵖ C D).obj rT)
      (qS := (Functor.whiskeringRight ℕᵒᵖ C A).obj qS)
      (qR := (Functor.whiskeringRight ℕᵒᵖ D B).obj qR)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso d)
      (adjS.whiskerRight ℕᵒᵖ) (adjR.whiskerRight ℕᵒᵖ) := by
  constructor
  · intro N
    ext n
    simpa [Adjunction.whiskerRight] using he.1 (N.obj n)
  · intro Q
    ext n
    simpa [Adjunction.whiskerRight] using he.2 (Q.obj n)

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} B]
  [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wA} D]
  [PreservesFiniteLimits JS] [PreservesFiniteColimits JS]
  [PreservesFiniteLimits JR] [PreservesFiniteColimits JR]
  [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
  [PreservesFiniteLimits rT] [PreservesFiniteColimits rT]
  [PreservesFiniteLimits qS] [PreservesFiniteColimits qS]
  [PreservesFiniteLimits qR] [PreservesFiniteColimits qR]

private theorem cbcDerivedSquare_symm :
    cbcDerivedSquare rU JR JS rT e.symm = (cbcDerivedSquare JS rT rU JR e).symm := by
  apply Iso.ext
  simp only [cbcDerivedSquare, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapDerivedCategoryNatIso_symm, Iso.symm_inv, Category.assoc]

private theorem equations_derived (he : CbcAdjunctionCompatible e d adjS adjR) :
    CbcAdjunctionCompatible (cbcDerivedSquare JS rT rU JR e) (cbcDerivedSquare rT qR qS rU d)
      (OpenTensorNormalization.exactDerivedAdjunction adjS)
      (OpenTensorNormalization.exactDerivedAdjunction adjR) := by
  have hm := inverseMate_of_unit e d adjS adjR he.1
  have : IsIso
      ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.symm.hom)).natTrans := by
    change IsIso ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.inv)).natTrans
    rw [hm]
    infer_instance
  have hiso : asIso
      ((mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.symm.hom)).natTrans = e.symm := by
    apply Iso.ext
    exact hm
  have hd := (exact_localization_inverse_mate adjS adjR d.symm).2.1
  rw [hiso] at hd
  change ((mateEquiv (OpenTensorNormalization.exactDerivedAdjunction adjS)
      (OpenTensorNormalization.exactDerivedAdjunction adjR)).symm
      (TwoSquare.mk _ _ _ _ (cbcDerivedSquare qS rU rT qR d.symm).hom)).natTrans =
        (cbcDerivedSquare rU JR JS rT e.symm).hom at hd
  rw [cbcDerivedSquare_symm, cbcDerivedSquare_symm] at hd
  exact equations_of_inverseMate _ _ _ _ hd

end EquationCalculus

section
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasLimits A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

end
section CoherenceHelpers
universe v w u' v' w' c h r
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem restriction_identity {C : Type c} [Category.{h} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c h r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r}]
    {R S : Sheaf J CommRingCat.{max c h r}} (U : C) (a : R ⟶ S)
    (M : SheafOfModules.{max c h r} (RingedOpenScalar.rings S)) (V : (Over U)ᵒᵖ)
    (x : (((RingedOpenScalar.scalars.{c, h, r} a) ⋙
      localizedSystemRestriction.{c, h, r} R U).obj M).val.obj V) :
    ((RingedOpenScalar.restrictionIso.{c, h, r} U a).hom.app M).val.app V x = x := by
  rfl

private theorem exactProducts_of_epi {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A]
    (he : ∀ (X Y : ℕ → A) (f : ∀ n, X n ⟶ Y n),
      (∀ n, Epi (f n)) → Epi (Limits.Pi.map f)) : HasExactLimitsOfShape (Discrete ℕ) A := by
  let : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms := ⟨fun {X Y} f hf ↦ by
    have : ∀ n : ℕ, Epi (f.app ⟨n⟩) := fun n ↦ inferInstance
    have : Epi (Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩)) := he _ _ _ this
    have hmap : lim.map f = (Pi.isoLimit X).inv ≫
        Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit Y).hom := by
      apply limit.hom_ext
      rintro ⟨n⟩
      simp only [Category.assoc, Pi.isoLimit_hom_π, Limits.Pi.map_π,
        Pi.isoLimit_inv_π_assoc]
      exact limMap_π f ⟨n⟩
    rw [hmap]
    infer_instance
  ⟩
  exact hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)

private theorem towerGrothendieck {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] :
    IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{v, v} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{v, v} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

section Normalization
open NormalizedLimitSquare RoosAdjunctionUnit
variable {A : Type u} [Category.{v} A] [Abelian A] [HasLimits A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)]
  {LA : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A}
  {etaA : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA}

private theorem corner_unit (a : Corner LA etaA)
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    etaA.app X ≫ a.theta.hom.app (DerivedCategory.Q.obj X) ≫ a.factors.hom.app X =
      DerivedCategory.Q.map (roosι X) := by
  let T := CochainComplex.kInjectiveResolutionFunctor.{v} (ℕᵒᵖ ⥤ A)
  let q : X ⟶ T.obj X := (CochainComplex.toKInjectiveResolution.{v} (ℕᵒᵖ ⥤ A)).app X
  have : QuasiIso q := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2
  let theta : DerivedCategory.Q ⋙ LA ≅ roosF ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q a.theta ≪≫ a.factors
  have htheta : LA.map (DerivedCategory.Q.map q) ≫ theta.hom.app (T.obj X) =
      theta.hom.app X ≫ DerivedCategory.Q.map (roosF.map q) := theta.hom.naturality q
  have heta : DerivedCategory.Q.map (roosLimitFunctor.map q) ≫ etaA.app (T.obj X) =
      etaA.app X ≫ LA.map (DerivedCategory.Q.map q) := etaA.naturality q
  have hq : IsIso (DerivedCategory.Q.map (roosF.map q)) := by
    have he : DerivedCategory.Q.map (roosF.map q) =
        theta.inv.app X ≫ LA.map (DerivedCategory.Q.map q) ≫ theta.hom.app (T.obj X) := by
      rw [htheta, Iso.inv_hom_id_app_assoc]
    rw [he]
    infer_instance
  change etaA.app X ≫ theta.hom.app X = _
  apply (cancel_mono (DerivedCategory.Q.map (roosF.map q))).mp
  have hn := a.normalization (T.obj X) (fun _ ↦ inferInstance)
  change etaA.app (T.obj X) ≫ theta.hom.app (T.obj X) = _ at hn
  calc
    _ = etaA.app X ≫ LA.map (DerivedCategory.Q.map q) ≫ theta.hom.app (T.obj X) := by
      rw [Category.assoc, ← htheta]
    _ = DerivedCategory.Q.map (roosLimitFunctor.map q) ≫
        etaA.app (T.obj X) ≫ theta.hom.app (T.obj X) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ theta.hom.app (T.obj X)) heta.symm
    _ = _ := by
      rw [hn]
      exact (DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Q.map (roosι_natural q)).trans
          (DerivedCategory.Q.map_comp _ _))

variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasLimits B]
  [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w'} (ℕᵒᵖ ⥤ B)]
  {LB : DerivedCategory.{w'} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w'} B}
  {etaB : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB}
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)] in
private theorem inclusion_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosι X).f (p + 1) ≫ (coordinates X p).hom =
      biprod.lift ((Limits.Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n))).f (p + 1)) 0 := by
  dsimp only [coordinates, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, roosι_χ]
  apply biprod.hom_ext <;> simp [Category.assoc]

omit [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)] in
private theorem comparison_inclusion (a : Corner LA etaA) (b : Corner LB etaB)
    (c : Comparison a b F) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosι X) ≫ c.kappa.hom.app X =
      limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone (limit.cone X.asFunctor)) ≫
        roosι ((towerComplex F).obj X) := by
  apply HomologicalComplex.Hom.ext
  funext i
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  apply (cancel_mono (coordinates ((towerComplex F).obj X) p).hom).mp
  simp only [HomologicalComplex.comp_f, Category.assoc, Functor.mapHomologicalComplex_map_f]
  rw [c.coordinate_formula, ← Category.assoc, ← Category.assoc, ← F.map_comp,
    inclusion_coordinates, Category.assoc, inclusion_coordinates]
  apply biprod.hom_ext
  · simp only [Category.assoc]
    erw [biprod.map_fst]
    simp only [← Category.assoc, Functor.biprodComparison_fst]
    rw [← F.map_comp, biprod.lift_fst]
    simp only [Category.assoc, biprod.lift_fst]
    apply (cancel_mono (piComparison (HomologicalComplex.eval B (.up ℤ) (p + 1))
      (fun n : ℕ ↦ ((towerComplex F).obj X).asFunctor.obj (op n)))).mp
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π, HomologicalComplex.eval_map]
    change ((F.mapHomologicalComplex (.up ℤ)).map
        (Limits.Pi.lift (fun n : ℕ ↦ limit.π X.asFunctor (op n)))).f (p + 1) ≫
      (piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1) ≫
      (Pi.π (fun n : ℕ ↦ ((towerComplex F).obj X).asFunctor.obj (op n)) n).f
        (p + 1) = _
    have hc := congrArg (fun z ↦ z.f (p + 1))
      (piComparison_comp_π (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ X.asFunctor.obj (op n)) n)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hc
    erw [hc]
    change F.map ((Limits.Pi.lift (fun n : ℕ ↦
      limit.π X.asFunctor (op n))).f (p + 1)) ≫
        F.map ((Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f (p + 1)) = _
    rw [← F.map_comp, ← HomologicalComplex.comp_f, Limits.Pi.lift_comp_π]
    have hb := congrArg (fun z ↦ z.f (p + 1))
      (limit.lift_π ((F.mapHomologicalComplex (.up ℤ)).mapCone
        (limit.cone X.asFunctor)) (op n))
    erw [← HomologicalComplex.comp_f, Limits.Pi.lift_comp_π]
    exact hb.symm
  · simp only [Category.assoc]
    erw [biprod.map_snd]
    simp only [← Category.assoc, Functor.biprodComparison_snd]
    rw [← F.map_comp, biprod.lift_snd, F.map_zero, zero_comp]
    simp only [Category.assoc, biprod.lift_snd, comp_zero]

private theorem comparison_normalized
    [IsGrothendieckAbelian.{v'} (ℕᵒᵖ ⥤ B)]
    (a : Corner LA etaA) (b : Corner LB etaB) (c : Comparison a b F) :
    CbcLimitNormalized F LA LB etaA etaB c.lambda := by
  constructor
  intro X
  let Y := (towerComplex F).obj X
  let beta := limit.lift _ ((F.mapHomologicalComplex (.up ℤ)).mapCone
    (limit.cone X.asFunctor))
  apply (cancel_mono (b.theta.hom.app (DerivedCategory.Q.obj Y) ≫ b.factors.hom.app Y)).mp
  simp only [Category.assoc]
  erw [reassoc_of% (b.theta.hom.naturality ((towerFactors F).hom.app X))]
  rw [c.conjugation]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  dsimp only [Y]
  erw [← c.descent X]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, corner_unit]
  simp only [Category.assoc]
  rw [corner_unit a X]
  rw [reassoc_of% (F.mapDerivedCategoryFactors.hom.naturality (roosι X))]
  rw [← DerivedCategory.Q.map_comp, comparison_inclusion F a b c X,
    DerivedCategory.Q.map_comp]

end Normalization
end CoherenceHelpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section CoherentNormalization
variable {A B C D : Type uA} [Category.{vA} A] [Category.{vA} B]
  [Category.{vA} C] [Category.{vA} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasLimits A] [HasLimits B] [HasLimits C] [HasLimits D]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} B]
  [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wA} D]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ D)]
  [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ A)] [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ B)]
  [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ C)] [IsGrothendieckAbelian.{vA} (ℕᵒᵖ ⥤ D)]
  {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {K : C ⥤ D}
  [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  {LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A}
  {LB : DerivedCategory.{wA} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wA} B}
  {LC : DerivedCategory.{wA} (ℕᵒᵖ ⥤ C) ⥤ DerivedCategory.{wA} C}
  {LD : DerivedCategory.{wA} (ℕᵒᵖ ⥤ D) ⥤ DerivedCategory.{wA} D}
  {etaA : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LA}
  {etaB : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LB}
  {etaC : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LC}
  {etaD : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LD}
  {e : F ⋙ G ≅ H ⋙ K}

end CoherentNormalization

end CategoryTheory

namespace AlgebraicGeometry.Scheme

attribute [local instance] WeilConjectures.sfAbBijective

variable {T : Scheme.{u}} (U : T.ProEt)
  {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)

variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
  U))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over
    U))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
  U))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients S).over
    U))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))]
variable [HasDerivedCategory.{wA} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{u + 1} (proEtaleModuleCoefficients S))]

attribute [local irreducible] localizedSystemAdjunction
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
attribute [local irreducible] Functor.mapDerivedCategoryNatIso
  RingedOpenScalar.derivedSquare cbcDerivedSquare

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
attribute [local instance] WeilConjectures.sfAbBijective
private theorem ambient_exact (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u + 1}
      (proEtaleModuleCoefficients R)) := by
  let : Abelian (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)) :=
    RingedOpenScalar.ambientAbelian.{u + 1, u, 0} _
  apply CategoryTheory.exactProducts_of_epi
  intro X Y f hf
  exact (ProEt.countableProducts_exact.{u, 0, 0} T R).2.2 ℕ X Y f hf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] cbcDerivedTowerSquare Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapHomologicalComplex NatIso.mapHomologicalComplex

end AlgebraicGeometry.Scheme
