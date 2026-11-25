/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.CategoryTheory.Monoidal.DerivedBraided
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
public import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.RestrictScalarsBraided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import all WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import all WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.CategoryTheory.Normalized.NormalizedBraidedLocalization
import all WeilConjectures.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
import all WeilConjectures.CategoryTheory.CountableTensorStructures.CountableTensorStructuresSupplement
import all WeilConjectures.Algebra.Homology.AdditiveTotalTensorConeComparison
import all WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
import all WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import all Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor

/-! # Constant scalar restriction and tensor products

Source: Stacks Project, Modules on Sites, Tags 03CY and 0GMW, and Cohomology on Sites,
Tags 06YN, 06YP, 06YS, 0G7D, 06YT and 06YU
(blueprint: lem-sfb-constant-scalar-restriction-tensor).

The coefficient-sized small site implements the size convention. The restriction is the
existing literal restriction along the constant commutative-ring sheafification unit.

## Main statements

* `ordinary_exists`: normalized ordinary symmetric monoidal equivalence.
* `total_symmetry`: coherence of the existing canonical signed-total comparison.
* `flat_iff`, `kflat_iff`: preservation and reflection of the two flatness conditions.
* `derived_comparison`: the normalized coherent comparison on unbounded derived tensors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v wR wB dU dV dW

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.ConstantScalarRestriction

private theorem flat_equivalence {D : Type dU} {E : Type u}
    [Category.{dV} D] [Category.{v} E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.Monoidal] [F.IsEquivalence] (M : D) :
    ObjectProperty.flat M ↔ ObjectProperty.flat (F.obj M) := by
  let : F.PreservesFlat := F.preservesFlat_of_isEquivalence
  let : F.asEquivalence.functor.Monoidal := inferInstanceAs F.Monoidal
  let : F.inv.Monoidal := F.asEquivalence.inverseMonoidal
  let : F.inv.PreservesFlat := F.inv.preservesFlat_of_isEquivalence
  refine ⟨Functor.PreservesFlat.flat_obj, fun h ↦ ?_⟩
  exact ObjectProperty.prop_of_iso _ (F.asEquivalence.unitIso.app M).symm
    (Functor.PreservesFlat.flat_obj (F := F.inv) h)

private theorem flatResolutionTransport
    {D : Type*} {E : Type*} [Category* D] [Category* E]
    [Abelian D] [Abelian E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.Additive] [F.Monoidal] [F.IsEquivalence]
    [Abelian.HasFunctorialFlatResolution D] :
    Abelian.HasFunctorialFlatResolution E := by
  let e := F.asEquivalence
  obtain ⟨L⟩ := (inferInstance : Abelian.HasFunctorialFlatResolution D)
  refine ⟨{
    F := ObjectProperty.lift _ (e.inverse ⋙ L.F ⋙ ObjectProperty.flat.ι ⋙ F)
      (fun X ↦ (flat_equivalence F _).mp (L.F.obj (e.inverse.obj X)).property)
    π := ?_
    epi_π_app := ?_ }⟩
  · exact { app X := F.map (L.π.app (e.inverse.obj X)) ≫ e.counitIso.hom.app X
            naturality X Y f := by
              change F.map (L.F.map (e.inverse.map f)).hom ≫
                F.map (L.π.app (e.inverse.obj Y)) ≫ e.counitIso.hom.app Y =
                  (F.map (L.π.app (e.inverse.obj X)) ≫ e.counitIso.hom.app X) ≫ f
              have hn := L.π.naturality (e.inverse.map f)
              change (L.F.map (e.inverse.map f)).hom ≫ L.π.app (e.inverse.obj Y) =
                L.π.app (e.inverse.obj X) ≫ e.inverse.map f at hn
              rw [← F.map_comp_assoc, hn, F.map_comp, Category.assoc]
              simpa only [e, Functor.asEquivalence, Functor.comp_map,
                Functor.id_map, Category.assoc] using
                congrArg (F.map (L.π.app (e.inverse.obj X)) ≫ ·)
                  (e.counitIso.hom.naturality f) }
  · intro X
    change Epi (F.map (L.π.app (e.inverse.obj X)) ≫ e.counitIso.hom.app X)
    infer_instance

attribute [local instance] complexTensorMemo derivedTensorMemo

/-- The canonical localization tensor square on every pair of K-flat representatives.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def derivedTensorCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal]
    (κ : CochainComplex D ℤ → Prop)
    (monoidal : G.mapDerivedCategory.Monoidal) : Prop :=
  ∀ (P Q : CochainComplex D ℤ), κ P → κ Q →
    @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G.mapDerivedCategory
        monoidal.toOplaxMonoidal (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
      (G.mapDerivedCategoryFactors.hom.app P ⊗ₘ G.mapDerivedCategoryFactors.hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
      DerivedCategory.Q.map (Functor.mapCochainComplexμIso G P Q).inv

/-- Compatibility of the derived tensor comparison with the canonical Koszul braiding.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def derivedSymmetryCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence]
    (monoidal : G.mapDerivedCategory.Monoidal) : Prop :=
  ∀ (X Y : DerivedCategory D),
    G.mapDerivedCategory.map
        (DerivedMonoidal.braiding' (DerivedCategory.Qh (C := D))
          (HomotopyCategory.quasiIso D (.up ℤ)) X Y).hom ≫
        @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G.mapDerivedCategory
          monoidal.toOplaxMonoidal Y X =
      @Functor.OplaxMonoidal.δ _ _ _ _ _ _ G.mapDerivedCategory
          monoidal.toOplaxMonoidal X Y ≫
        (DerivedMonoidal.braiding' (DerivedCategory.Qh (C := E))
          (HomotopyCategory.quasiIso E (.up ℤ))
          (G.mapDerivedCategory.obj X) (G.mapDerivedCategory.obj Y)).hom

/-- The degree-zero regular-unit normalization of the derived tensor comparison.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def derivedUnitCompatibility
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal]
    (monoidal : G.mapDerivedCategory.Monoidal) : Prop :=
  @Functor.LaxMonoidal.ε _ _ _ _ _ _ G.mapDerivedCategory
        monoidal.toLaxMonoidal ≫
      G.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      G.mapDerivedCategoryFactors.hom.app (𝟙_ _) =
    Functor.LaxMonoidal.ε DerivedCategory.Q ≫
      DerivedCategory.Q.map (Functor.LaxMonoidal.ε (G.mapHomologicalComplex (.up ℤ)))

/-- The monoidal structure and its specified tensor, symmetry and unit laws.
The subtype stores the same comparison data using the existing logical constructors.
Source: Stacks 06YU (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def DerivedComparisonData
    (D : Type dU) (E : Type u) [Category.{dV} D] [Category.{v} E]
    [Abelian D] [Abelian E] [IsGrothendieckAbelian.{dV} D]
    [IsGrothendieckAbelian.{v} E]
    [HasColimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} E]
    [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalClosed D] [MonoidalClosed E]
    [MonoidalPreadditive D] [MonoidalPreadditive E]
    [BraidedCategory D] [BraidedCategory E]
    [Abelian.HasFunctorialFlatResolution D] [Abelian.HasFunctorialFlatResolution E]
    [HasDerivedCategory.{wR} D] [HasDerivedCategory.{wB} E]
    (G : D ⥤ E) [G.Additive] [G.IsEquivalence] [G.Monoidal]
    (κ : CochainComplex D ℤ → Prop) :=
  { monoidal : G.mapDerivedCategory.Monoidal //
    derivedTensorCompatibility D E G κ monoidal ∧
    derivedSymmetryCompatibility D E G monoidal ∧
    derivedUnitCompatibility D E G monoidal }

section DerivedComparisonProof


set_option backward.isDefEq.respectTransparency true
open CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal

universe uD vD wD uE vE wE
variable {D : Type uD} [Category.{vD} D] [Abelian D] [IsGrothendieckAbelian.{vD} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory.{wD} D]
  [HasColimitsOfSize.{0, 0} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [IsGrothendieckAbelian.{vE} E]
  [MonoidalCategory E] [SymmetricCategory E] [MonoidalClosed E] [MonoidalPreadditive E]
  [Abelian.HasFunctorialFlatResolution E] [HasDerivedCategory.{wE} E]
  [HasColimitsOfSize.{0, 0} E]

private theorem nativeTensorIso (P Q : CochainComplex D ℤ)
    (hQ : Q.IsKFlatForTotalTensor) : IsIso (μ DerivedCategory.Q P Q) := by
  have : IsIso (μ DerivedCategory.Qh
      ((HomotopyCategory.quotient D (.up ℤ)).obj P)
      ((HomotopyCategory.quotient D (.up ℤ)).obj Q)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso D (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  change IsIso ((_ ⊗ₘ _) ≫
    (μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

end DerivedComparisonProof

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (B : Type (max u v)) [CommRing B]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def restrictCancelIso {R S : Sheaf J RingCat.{max u v}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{max u v} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

set_option warn.classDefReducibility false in
private def monoidalKeepingLax
    {D E : Type*} [Category* D] [Category* E]
    [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.LaxMonoidal] [IsIso (Functor.LaxMonoidal.ε F)]
    [∀ X Y, IsIso (Functor.LaxMonoidal.μ F X Y)] : F.Monoidal :=
  { (Functor.Monoidal.ofLaxMonoidal F) with toLaxMonoidal := inferInstance }

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

section OrdinaryProof
set_option warn.classDefReducibility false
private def scalarUnit :
    (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B)) ≫
    ((constantCommuteCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv.app
      (CommRingCat.of B)).hom

private def scalarMap (U : Cᵒᵖ) : B →+* (ring J B).obj.obj U :=
  ((scalarUnit J B).app U).hom

attribute [local irreducible] ring

section GenericRaw

private def constantToFunctor :
    PresheafOfModules.{max u v}
      (((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) ⋙ forget₂ CommRingCat RingCat) ⥤
        Cᵒᵖ ⥤ ModuleCat.{max u v} B where
  obj P :=
    { obj := P.obj
      map := fun f ↦ P.map f
      map_id := fun X ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_id X)
      map_comp := fun f g ↦ by ext x; exact P.map_comp_apply f g x }
  map f :=
    { app := f.app
      naturality := fun _ _ g ↦ by ext x; exact PresheafOfModules.naturality_apply f g x }

set_option backward.isDefEq.respectTransparency false in
private def constantToFunctorLax : (constantToFunctor (C := C) B).LaxMonoidal where
  ε := { app X := 𝟙 _ }
  μ M N := { app X := 𝟙 _ }
  μ_natural_left := by intros; ext X x; rfl
  μ_natural_right := by intros; ext X x; rfl
  associativity := by
    intro M N P
    apply NatTrans.ext
    funext X
    change (𝟙 _ ▷ P.obj X) ≫ 𝟙 _ ≫ (α_ M N P).hom.app X =
      (α_ (M.obj X) (N.obj X) (P.obj X)).hom ≫ (M.obj X ◁ 𝟙 _) ≫ 𝟙 _
    simpa only [Category.id_comp, Category.comp_id,
      MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id] using
      (PresheafOfModules.associator_hom_app M N P X)
  left_unitality := by
    intro M
    apply NatTrans.ext
    funext X
    change (λ_ (M.obj X)).hom =
      (𝟙 _ ▷ M.obj X) ≫ 𝟙 _ ≫ (λ_ M).hom.app X
    simpa only [Category.id_comp, Category.comp_id,
      MonoidalCategory.id_whiskerRight] using
      (PresheafOfModules.leftUnitor_hom_app M X).symm
  right_unitality := by
    intro M
    apply NatTrans.ext
    funext X
    change (ρ_ (M.obj X)).hom =
      (M.obj X ◁ 𝟙 _) ≫ 𝟙 _ ≫ (ρ_ M).hom.app X
    simpa only [Category.id_comp, Category.comp_id,
      MonoidalCategory.whiskerLeft_id] using
      (PresheafOfModules.rightUnitor_hom_app M X).symm

attribute [local instance] constantToFunctorLax

set_option backward.isDefEq.respectTransparency false in
private def rawRestrictionGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat) :
    PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      Cᵒᵖ ⥤ ModuleCat.{max u v} B :=
  PresheafOfModules.restrictScalars ι ⋙ constantToFunctor B

set_option backward.isDefEq.respectTransparency false in
private def rawLaxGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat) :
    (rawRestrictionGeneric B R ι).LaxMonoidal :=
  letI : MonoidalCategory (PresheafOfModules.{max u v}
      ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModules.{max u v}
      (((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) ⋙ forget₂ CommRingCat RingCat)))
  letI := PresheafOfModules.restrictScalarsLaxMonoidal
    (R := (Functor.const Cᵒᵖ).obj (CommRingCat.of B)) (R' := R) ι
  letI : (constantToFunctor (C := C) B).LaxMonoidal := constantToFunctorLax B
  Functor.LaxMonoidal.comp
    (PresheafOfModules.restrictScalars ι) (constantToFunctor B)

attribute [local instance] rawLaxGeneric

private def rawTensorGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat)
    (M N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)) :
    (rawRestrictionGeneric B R ι).obj M ⊗ (rawRestrictionGeneric B R ι).obj N ⟶
      (rawRestrictionGeneric B R ι).obj (M ⊗ N) :=
  Functor.LaxMonoidal.μ (rawRestrictionGeneric B R ι) M N

set_option backward.isDefEq.respectTransparency false in
private def rawBraidedGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat) :
    (rawRestrictionGeneric B R ι).LaxBraided where
  braided M N := by
    apply NatTrans.ext
    funext X
    let : CommRing (((Functor.const Cᵒᵖ).obj (RingCat.of B)).obj X) :=
      inferInstanceAs (CommRing B)
    change (𝟙 _ ≫ Functor.LaxMonoidal.μ
        (ModuleCat.restrictScalars (ι.app X).hom) (M.obj X) (N.obj X)) ≫
        (ModuleCat.restrictScalars (ι.app X).hom).map (β_ (M.obj X) (N.obj X)).hom =
      (β_ _ _).hom ≫ (𝟙 _ ≫ Functor.LaxMonoidal.μ
        (ModuleCat.restrictScalars (ι.app X).hom) (N.obj X) (M.obj X))
    simpa only [Category.id_comp] using
      Functor.LaxBraided.braided
        (F := ModuleCat.restrictScalars (ι.app X).hom) (M.obj X) (N.obj X)

end GenericRaw

private def rawRestriction :
    PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj ⥤
      Cᵒᵖ ⥤ ModuleCat.{max u v} B := rawRestrictionGeneric B (ring J B).obj (scalarUnit J B)

private def rawTensor
    (M N : PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj) :
    (rawRestriction J B).obj M ⊗ (rawRestriction J B).obj N ⟶
      (rawRestriction J B).obj (M ⊗ N) :=
   rawTensorGeneric B (ring J B).obj (scalarUnit J B) M N

@[instance_reducible]
private def rawLax : (rawRestriction J B).LaxMonoidal :=
  rawLaxGeneric B (ring J B).obj (scalarUnit J B)

attribute [local instance] rawLax

@[instance_reducible]
private def rawBraided : (rawRestriction J B).LaxBraided :=
  rawBraidedGeneric B (ring J B).obj (scalarUnit J B)

private abbrev moduleInclusion : Modules J B ⥤
    PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)

@[instance_reducible]
private def moduleInclusionLax : (moduleInclusion J B).LaxMonoidal :=
  (PresheafOfModules.sheafificationAdjunction.{max u v}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
      (ring J B)).obj)).rightAdjointLaxMonoidal

attribute [local instance] moduleInclusionLax

private def moduleInclusionBraided : (moduleInclusion J B).LaxBraided :=
  (PresheafOfModules.sheafificationAdjunction.{max u v}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
      (ring J B)).obj)).rightAdjointLaxBraided

set_option backward.isDefEq.respectTransparency true in
private def restrictionPresheafIso :
    moduleInclusion J B ⋙ rawRestriction J B ≅
      restriction J B ⋙ sheafToPresheaf J (ModuleCat.{max u v} B) :=
  NatIso.ofComponents (fun M ↦
    { hom :=
        { app X := ModuleCat.ofHom
            (X := ((moduleInclusion J B ⋙ rawRestriction J B).obj M).obj X)
            (Y := ((restriction J B ⋙ sheafToPresheaf J
              (ModuleCat.{max u v} B)).obj M).obj X)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          naturality _ _ _ := by ext x; rfl }
      inv :=
        { app X := ModuleCat.ofHom
            (X := ((restriction J B ⋙ sheafToPresheaf J
              (ModuleCat.{max u v} B)).obj M).obj X)
            (Y := ((moduleInclusion J B ⋙ rawRestriction J B).obj M).obj X)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          naturality _ _ _ := by ext x; rfl }
      hom_inv_id := by ext X x; rfl
      inv_hom_id := by ext X x; rfl }) (fun _ ↦ by ext X x; rfl)

private def fixedSheafificationMonoidal :
    (presheafToSheaf J (ModuleCat.{max u v} B)).Monoidal :=
  (sfbSheafTensorStructure (A := ModuleCat.{max u v} B) J).sheafificationMonoidal

attribute [local instance] fixedSheafificationMonoidal

private def fixedSheafificationBraided :
    (presheafToSheaf J (ModuleCat.{max u v} B)).Braided :=
  (sfbSheafTensorStructure (A := ModuleCat.{max u v} B) J).sheafificationBraided

attribute [local instance] fixedSheafificationBraided

private def restrictionSheafifiedIso :
    (moduleInclusion J B ⋙ rawRestriction J B) ⋙ presheafToSheaf J (ModuleCat.{max u v} B) ≅
      restriction J B :=
  Functor.isoWhiskerRight (restrictionPresheafIso J B) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (sheafificationAdjunction J (ModuleCat.{max u v} B)).counit) ≪≫
    (restriction J B).rightUnitor

private def ordinaryLax : (restriction J B).LaxMonoidal := by
  letI := rawLax J B
  letI := moduleInclusionLax J B
  letI := fixedSheafificationMonoidal J B
  exact Functor.LaxMonoidal.transport (restrictionSheafifiedIso J B)

attribute [local instance] ordinaryLax

private theorem scalarUnit_surjective : Presheaf.IsLocallySurjective J (scalarUnit J B) := by
  unfold scalarUnit
  unfold ring
  infer_instance

attribute [local instance] scalarUnit_surjective

set_option backward.isDefEq.respectTransparency false in
private theorem pairing_smul_left (M N H : Modules J B)
    (b : ∀ X : Cᵒᵖ, ((restriction J B).obj M).obj.obj X →ₗ[B]
      ((restriction J B).obj N).obj.obj X →ₗ[B] ((restriction J B).obj H).obj.obj X)
    (hb : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X),
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y))
    (X : Cᵒᵖ) (r : (ring J B).obj.obj X) (x : M.val.obj X) (y : N.val.obj X) :
    b X (r • x) y = r • (show H.val.obj X from b X x y) := by
  apply H.isSheaf.isSeparated _ (Presheaf.imageSieve (scalarUnit J B) r)
    (Presheaf.imageSieve_mem J (scalarUnit J B) r)
  rintro Y f ⟨a, ha⟩
  change H.val.map f.op (b X (r • x) y) = H.val.map f.op (r • (show H.val.obj X from b X x y))
  rw [← hb, H.val.map_smul, M.val.map_smul, ← ha, ← hb]
  exact congrArg (fun k ↦ k (N.val.map f.op y))
    ((b (Opposite.op Y)).map_smul a (M.val.map f.op x))

set_option backward.isDefEq.respectTransparency false in
private def upgradePairing (M N H : Modules J B)
    (b : ∀ X : Cᵒᵖ, ((restriction J B).obj M).obj.obj X →ₗ[B]
      ((restriction J B).obj N).obj.obj X →ₗ[B] ((restriction J B).obj H).obj.obj X)
    (hb : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X),
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y))
    (X : Cᵒᵖ) : M.val.obj X →ₗ[(ring J B).obj.obj X]
      N.val.obj X →ₗ[(ring J B).obj.obj X] H.val.obj X where
  toFun x :=
    { toFun := b X x
      map_add' := (b X x).map_add
      map_smul' := fun r y ↦ by
        let b' := fun Y ↦ (b Y).flip
        exact pairing_smul_left J B N M H b' (fun f y x ↦ hb f x y) X r y x }
  map_add' := fun x x' ↦ by ext y; exact congrArg (fun k ↦ k y) ((b X).map_add x x')
  map_smul' := fun r x ↦ by ext y; exact pairing_smul_left J B M N H b hb X r x y

set_option backward.isDefEq.respectTransparency false in
private def ringTensorLift (M N H : Modules J B)
    (b : ∀ X : Cᵒᵖ, M.val.obj X →ₗ[(ring J B).obj.obj X]
      N.val.obj X →ₗ[(ring J B).obj.obj X] H.val.obj X)
    (hb : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X),
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y)) :
    M ⊗ N ⟶ H :=
  (SheafOfModules.CochainScalarConstruction.cochain_tensor_bilinear_universal
    (ring J B) M N H b hb).choose

set_option backward.isDefEq.respectTransparency false in
private theorem ringTensorLift_pure (M N H : Modules J B)
    (b : ∀ X : Cᵒᵖ, M.val.obj X →ₗ[(ring J B).obj.obj X]
      N.val.obj X →ₗ[(ring J B).obj.obj X] H.val.obj X)
    (hb : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X),
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (ringTensorLift J B M N H b hb).val.app U (ringPure J B M N U x y) = b U x y :=
  (SheafOfModules.CochainScalarConstruction.cochain_tensor_bilinear_universal
    (ring J B) M N H b hb).choose_spec.1 U x y

set_option backward.isDefEq.respectTransparency false in
private theorem ringTensor_ext (M N H : Modules J B) (f g : M ⊗ N ⟶ H)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (ringPure J B M N U x y) =
        g.val.app U (ringPure J B M N U x y)) : f = g := by
  apply SheafOfModules.CochainScalarConstruction.pure_hom_ext (ring J B) M N H
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem fixedTensor_ext (M N H : Fixed J B) (f g : M ⊗ N ⟶ H)
    (h : ∀ (U : Cᵒᵖ) (x : M.obj.obj U) (y : N.obj.obj U),
      f.hom.app U (fixedPure J B M N U x y) =
        g.hom.app U (fixedPure J B M N U x y)) : f = g := by
  apply (cancel_epi (sfbSheafTensor_comparison J M N).inv).mp
  apply ((sheafificationAdjunction J (ModuleCat.{max u v} B)).homEquiv (M.obj ⊗ N.obj) H).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

set_option backward.isDefEq.respectTransparency true in
private theorem ringPure_inclusion (M N : Modules J B) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (Functor.LaxMonoidal.μ (moduleInclusion J B) M N).app U
      (x ⊗ₜ[(ring J B).obj.obj U] y) = ringPure J B M N U x y := by
  dsimp only [Functor.LaxMonoidal.μ, moduleInclusionLax]
  rw [Adjunction.homEquiv_unit]
  rfl

private def ordinaryLaxBraided : (restriction J B).LaxBraided := by
  letI := rawBraided J B
  letI := moduleInclusionBraided J B
  letI := Functor.LaxMonoidal.natTransIsMonoidal_of_transport
    (restrictionSheafifiedIso J B)
  exact Functor.LaxBraided.ofNatIso (restrictionSheafifiedIso J B)

private def fixedInclusionLax : (sheafToPresheaf J (ModuleCat.{max u v} B)).LaxMonoidal :=
  (sheafificationAdjunction J (ModuleCat.{max u v} B)).rightAdjointLaxMonoidal

attribute [local instance] fixedInclusionLax

set_option backward.isDefEq.respectTransparency false in
private theorem monoidalMate
    {X A D : Type*} [Category* X] [Category* A] [Category* D]
    [MonoidalCategory X] [MonoidalCategory A] [MonoidalCategory D]
    (H : X ⥤ A) (G : X ⥤ D) (a : A ⥤ D) (j : D ⥤ A)
    [H.LaxMonoidal] [a.Monoidal] [j.LaxMonoidal]
    (adj : a ⊣ j) [adj.IsMonoidal] [j.Full] [j.Faithful]
    (i : H ≅ G ⋙ j) :
    let e := Functor.isoWhiskerRight i a ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G (asIso adj.counit) ≪≫ G.rightUnitor
    letI : G.LaxMonoidal := Functor.LaxMonoidal.transport e
    NatTrans.IsMonoidal i.hom := by
  dsimp only
  let e := Functor.isoWhiskerRight i a ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft G (asIso adj.counit) ≪≫ G.rightUnitor
  let : G.LaxMonoidal := Functor.LaxMonoidal.transport e
  have := Functor.LaxMonoidal.natTransIsMonoidal_of_transport e
  let τ : H ⟶ G ⋙ j :=
    H.rightUnitor.inv ≫ Functor.whiskerLeft H adj.unit ≫
      (Functor.associator H a j).inv ≫ Functor.whiskerRight e.hom j
  have ht : NatTrans.IsMonoidal τ := by dsimp [τ]; infer_instance
  have he : τ = i.hom := by
    apply NatTrans.ext
    funext M
    dsimp [τ, e]
    simp only [Category.id_comp, Category.comp_id, j.map_comp]
    erw [← Category.assoc, adj.unit_naturality]
    erw [Category.assoc, adj.right_triangle_components, Category.comp_id]
  exact he ▸ ht

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionPresheafIso_monoidal :
    NatTrans.IsMonoidal (restrictionPresheafIso J B).hom := by
  exact monoidalMate (moduleInclusion J B ⋙ rawRestriction J B) (restriction J B)
    (presheafToSheaf J (ModuleCat.{max u v} B))
    (sheafToPresheaf J (ModuleCat.{max u v} B))
    (sheafificationAdjunction J (ModuleCat.{max u v} B)) (restrictionPresheafIso J B)

set_option backward.isDefEq.respectTransparency true in
private theorem fixedPure_inclusion (M N : Fixed J B) (U : Cᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    (Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{max u v} B)) M N).app U
      (x ⊗ₜ[B] y) = fixedPure J B M N U x y := by
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem restrictionPresheafIso_apply (M : Modules J B) (U : Cᵒᵖ)
    (x : ((moduleInclusion J B ⋙ rawRestriction J B).obj M).obj U) :
    ((restrictionPresheafIso J B).hom.app M).app U x = x := by rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rawRestriction_map_apply
    {M N : PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj}
    (f : M ⟶ N) (U : Cᵒᵖ) (x : M.obj U) :
    ((rawRestriction J B).map f).app U x = f.app U x := by rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rawTensor_pure
    (M N : PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj)
    (U : Cᵒᵖ) (x : M.obj U) (y : N.obj U) :
    (rawTensor J B M N).app U (x ⊗ₜ[B] y) = x ⊗ₜ[(ring J B).obj.obj U] y := by
  exact @ModuleCat.restrictScalars_μ_tmul B ((ring J B).obj.obj U) _ _
    (scalarMap J B U) (M.obj U) (N.obj U) x y

private theorem isoTensor_pure (M N : Modules J B) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : (((restrictionPresheafIso J B).hom.app M).app U ⊗ₘ
      ((restrictionPresheafIso J B).hom.app N).app U) (x ⊗ₜ[B] y) =
        (show ((restriction J B).obj M).obj.obj U from x) ⊗ₜ[B]
          (show ((restriction J B).obj N).obj.obj U from y) := by
  rfl

attribute [local irreducible] ordinaryLax ringPure fixedPure restrictionPresheafIso
set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_μ_pure (M N : Modules J B) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (Functor.LaxMonoidal.μ (restriction J B) M N).hom.app U
      (fixedPure J B ((restriction J B).obj M) ((restriction J B).obj N) U x y) =
      ringPure J B M N U x y := by
  have := restrictionPresheafIso_monoidal J B
  have h := NatTrans.IsMonoidal.tensor (τ := (restrictionPresheafIso J B).hom) M N
  have hh := congrArg (fun f ↦ f.app U (x ⊗ₜ[B] y)) h
  change ((restrictionPresheafIso J B).hom.app (M ⊗ N)).app U
    (((rawRestriction J B).map
      (Functor.LaxMonoidal.μ (moduleInclusion J B) M N)).app U
        ((rawTensor J B ((moduleInclusion J B).obj M)
          ((moduleInclusion J B).obj N)).app U (x ⊗ₜ[B] y))) =
    (Functor.LaxMonoidal.μ (restriction J B) M N).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{max u v} B))
        ((restriction J B).obj M) ((restriction J B).obj N)).app U
          ((((restrictionPresheafIso J B).hom.app M).app U ⊗ₘ
            ((restrictionPresheafIso J B).hom.app N).app U) (x ⊗ₜ[B] y))) at hh
  rw [rawTensor_pure, rawRestriction_map_apply, isoTensor_pure,
    restrictionPresheafIso_apply, ringPure_inclusion, fixedPure_inclusion] at hh
  exact hh.symm

attribute [local semireducible] ringPure fixedPure restrictionPresheafIso

set_option backward.isDefEq.respectTransparency true in
private def fixedPairing (M N : Fixed J B) (U : Cᵒᵖ) :
    M.obj.obj U →ₗ[B] N.obj.obj U →ₗ[B] (M ⊗ N).obj.obj U :=
  (TensorProduct.mk B _ _).compr₂
    (((sfbSheafTensor_comparison J M N).inv.hom.app U).hom.comp
      ((toSheafify J (M.obj ⊗ N.obj)).app U).hom)

set_option backward.isDefEq.respectTransparency true in
private theorem fixedPure_naturality (M N : Fixed J B) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    fixedPure J B M N V (M.obj.map f x) (N.obj.map f y) =
      (M ⊗ N).obj.map f (fixedPure J B M N U x y) := by
  let q := toSheafify J (M.obj ⊗ N.obj) ≫ (sfbSheafTensor_comparison J M N).inv.hom
  exact ConcreteCategory.congr_hom (q.naturality f) (x ⊗ₜ[B] y)

set_option backward.isDefEq.respectTransparency true in
private theorem restrictionTensor_ext (M N H : Modules J B)
    (f g : (restriction J B).obj (M ⊗ N) ⟶ (restriction J B).obj H)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.hom.app U (ringPure J B M N U x y) =
        g.hom.app U (ringPure J B M N U x y)) : f = g := by
  let F := restriction J B
  have hh : F.preimage f = F.preimage g := by
    apply ringTensor_ext J B M N H
    intro U x y
    change (F.map (F.preimage f)).hom.app U (ringPure J B M N U x y) =
      (F.map (F.preimage g)).hom.app U (ringPure J B M N U x y)
    simpa only [F.map_preimage] using h U x y
  simpa only [F.map_preimage] using congrArg F.map hh

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_μ_isIso (M N : Modules J B) :
    IsIso (Functor.LaxMonoidal.μ (restriction J B) M N) := by
  let F := restriction J B
  let H := F.objPreimage (F.obj M ⊗ F.obj N)
  let e : F.obj H ≅ F.obj M ⊗ F.obj N := F.objObjPreimageIso _
  let b (U : Cᵒᵖ) :=
    (fixedPairing J B (F.obj M) (F.obj N) U).compr₂ (e.inv.hom.app U).hom
  have hb {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.val.obj X) (y : N.val.obj X) :
      b Y (M.val.map f x) (N.val.map f y) = H.val.map f (b X x y) := by
    change e.inv.hom.app Y
      (fixedPure J B (F.obj M) (F.obj N) Y (M.val.map f x) (N.val.map f y)) = _
    erw [fixedPure_naturality]
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) _
  let q := ringTensorLift J B M N H (upgradePairing J B M N H b hb) hb
  have hq (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
      q.val.app U (ringPure J B M N U x y) = b U x y :=
    ringTensorLift_pure J B M N H _ hb U x y
  let r := F.map q ≫ e.hom
  have hr (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
      r.hom.app U (ringPure J B M N U x y) =
        fixedPure J B (F.obj M) (F.obj N) U x y := by
    change e.hom.hom.app U (q.val.app U (ringPure J B M N U x y)) = _
    rw [hq]
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom) e.inv_hom_id) U) _
  refine ⟨⟨r, ?_, ?_⟩⟩
  · apply fixedTensor_ext J B
    intro U x y
    change r.hom.app U
      ((Functor.LaxMonoidal.μ F M N).hom.app U (fixedPure J B _ _ U x y)) = _
    rw [ordinary_μ_pure, hr]
    rfl
  · apply restrictionTensor_ext J B M N (M ⊗ N)
    intro U x y
    change (Functor.LaxMonoidal.μ F M N).hom.app U
      (r.hom.app U (ringPure J B M N U x y)) = _
    rw [hr, ordinary_μ_pure]
    rfl

set_option backward.isDefEq.respectTransparency true in
private theorem ordinary_ε_isIso : IsIso (Functor.LaxMonoidal.ε (restriction J B)) := by
  let F := restriction J B
  let X := F.objPreimage (𝟙_ (Fixed J B))
  let e := F.objObjPreimageIso (𝟙_ (Fixed J B))
  have := ordinary_μ_isIso J B (𝟙_ (Modules J B)) X
  have h : IsIso (Functor.LaxMonoidal.ε F ▷ F.obj X) := by
    have hh : IsIso ((Functor.LaxMonoidal.ε F ▷ F.obj X) ≫
        Functor.LaxMonoidal.μ F (𝟙_ _) X ≫ F.map (λ_ X).hom) := by
      rw [← Functor.LaxMonoidal.left_unitality]
      infer_instance
    exact IsIso.of_isIso_comp_right (Functor.LaxMonoidal.ε F ▷ F.obj X)
      (Functor.LaxMonoidal.μ F (𝟙_ _) X ≫ F.map (λ_ X).hom)
  let i : tensorRight (F.obj X) ≅ 𝟭 (Fixed J B) :=
    (tensoringRight (Fixed J B)).mapIso e ≪≫ rightUnitorNatIso (Fixed J B)
  have : (tensorRight (F.obj X)).IsEquivalence := Functor.isEquivalence_of_iso i.symm
  have : IsIso ((tensorRight (F.obj X)).map (Functor.LaxMonoidal.ε F)) := h
  exact isIso_of_reflects_iso (Functor.LaxMonoidal.ε F) (tensorRight (F.obj X))

attribute [local semireducible] ring

set_option backward.isDefEq.respectTransparency true in
private theorem ordinary_ε_scalar (U : Cᵒᵖ) (b : B) :
    (Functor.LaxMonoidal.ε (restriction J B)).hom.app U (fixedUnitScalar J B U b) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b := by
  have := restrictionPresheafIso_monoidal J B
  have h := NatTrans.IsMonoidal.unit (τ := (restrictionPresheafIso J B).hom)
  have hh := congrArg (fun f ↦ f.app U b) h
  have hc := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of B) (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv
  have hu : (scalarUnit J B).app U b =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).app U b := by
    change ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B)) ≫
      sheafifyMap J
        (Functor.constComp Cᵒᵖ (CommRingCat.of B)
          (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv ≫
      (sheafifyComposeIso J (forget₂ CommRingCat.{max u v} RingCat.{max u v})
        ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))).hom).app U) b = _
    erw [← Category.assoc, ← hc, Category.assoc, sheafComposeIso_hom_fac]
    rfl
  change (Functor.LaxMonoidal.ε (rawRestriction J B) ≫
      (rawRestriction J B).map (Functor.LaxMonoidal.ε (moduleInclusion J B)) ≫
      (restrictionPresheafIso J B).hom.app (𝟙_ (Modules J B))).app U b =
    (Functor.LaxMonoidal.ε (sheafToPresheaf J (ModuleCat.{max u v} B)) ≫
      (sheafToPresheaf J (ModuleCat.{max u v} B)).map
        (Functor.LaxMonoidal.ε (restriction J B))).app U b at hh
  simp only [NatTrans.comp_app, ModuleCat.comp_apply] at hh
  change (Functor.LaxMonoidal.ε (moduleInclusion J B)).app U
      (Functor.LaxMonoidal.ε
        (ModuleCat.restrictScalars (scalarMap J B U)) b) =
    (Functor.LaxMonoidal.ε (restriction J B)).hom.app U
      ((Functor.LaxMonoidal.ε (sheafToPresheaf J (ModuleCat.{max u v} B))).app U b) at hh
  erw [@ModuleCat.restrictScalars_η B ((ring J B).obj.obj U) _ _
    (scalarMap J B U)] at hh
  have hm := (PresheafOfModules.sheafificationAdjunction.{max u v}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
      (ring J B)).obj)).right_triangle_components (𝟙_ (Modules J B))
  have hmm := congrArg (fun f ↦ f.app U ((scalarMap J B U) b)) hm
  change (Functor.LaxMonoidal.ε (moduleInclusion J B)).app U ((scalarMap J B U) b) =
    (scalarMap J B U) b at hmm
  rw [hmm] at hh
  have hf : (Functor.LaxMonoidal.ε (sheafToPresheaf J (ModuleCat.{max u v} B))).app U b =
      fixedUnitScalar J B U b := by rfl
  rw [hf] at hh
  exact hh.symm.trans hu

@[instance_reducible]
private def ordinaryMonoidal : (restriction J B).Monoidal := by
  have := ordinary_ε_isIso J B
  have := ordinary_μ_isIso J B
  exact monoidalKeepingLax (restriction J B)

end OrdinaryProof
variable [HasDerivedCategory.{wR} (Modules J B)] [HasDerivedCategory.{wB} (Fixed J B)]

/-- The induced equivalence of ordinary unbounded derived categories.
Source: Stacks 015F and 05RT (blueprint: lem-sfb-constant-scalar-restriction-tensor). -/
def onDerived : DerivedCategory (Modules J B) ⥤ DerivedCategory (Fixed J B) :=
  (restriction J B).mapDerivedCategory

/-- The normalized coherent comparison on ordinary unbounded K-flat derived tensors.
The monoidal structures here are the existing K-flat derived localization structures.
Source: Stacks 06YS, 0G7D, 06YT and 06YU
(blueprint: lem-sfb-constant-scalar-restriction-tensor).
The tensor square specifies the comparison on every pair of K-flat representatives,
using precisely `Functor.mapCochainComplexμIso` and the canonical localization maps.
The unit square fixes its normalization at the regular unit complex. -/
abbrev DerivedComparison :=
  DerivedComparisonData (Modules J B) (Fixed J B) (restriction J B)
    (fun P ↦ P.IsKFlatIndependentCoefficients)

end CategoryTheory.ConstantScalarRestriction
