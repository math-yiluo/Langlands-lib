/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import all WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
/-! # Uniqueness and the arbitrary-complex unit of scalar extension

## References

* Stacks 06YY, 07A6, and the representative equation in ScalarData
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} {R R' : Sheaf J CommRingCat.{r}} {φ : R ⟶ R'}

private theorem ordinary_unit_eq (S : ScalarData.{c, v, r} φ) :
    S.ordinaryAdjunction.unit = (SheafOfModules.sheafScalarOrdinaryAdjunction φ S.model).unit := by
  ext M U x
  have hs := S.unit_section M U x
  have hc := (Classical.choose_spec
    (SheafOfModules.sheafDerivedScalarAdjunction_exists φ S.model)).1 M U x
  have hi (y : (S.model.E.obj M).val.obj U) :
      (eqToHom (S.model.obj_eq M).symm).val.app U
        ((eqToHom (S.model.obj_eq M)).val.app U y) = y :=
    congrArg (fun a ↦ a.val.app U y) (eqToIso (S.model.obj_eq M)).hom_inv_id
  calc
    _ = (eqToHom (S.model.obj_eq M).symm).val.app U
        ((eqToHom (S.model.obj_eq M)).val.app U
          ((S.ordinaryAdjunction.unit.app M).val.app U x)) := (hi _).symm
    _ = (eqToHom (S.model.obj_eq M).symm).val.app U (extensionUnit φ M U x) :=
      congrArg _ hs
    _ = _ := hc.symm

private theorem unit_model_flat (S : ScalarData.{c, v, r} φ)
    (P : CochainComplex (Mod.{c, v, r} J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    S.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
      (res φ).mapDerivedCategory.map (S.model.ε.app P) ≫
      (res φ).mapDerivedCategoryFactors.hom.app
        ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have ht := S.transpose_model P ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P)
    hp (𝟙 _)
  rw [DerivedCategory.Q.map_id] at ht
  simp only [Adjunction.homEquiv_unit, resD] at ht
  repeat' first
    | erw [CategoryTheory.Functor.map_id] at ht
    | erw [Category.comp_id] at ht
  simpa only [Category.assoc] using ht

/-- The model-unit equation holds on arbitrary complexes, without flatness. -/
theorem ScalarData.unit_model (S : ScalarData.{c, v, r} φ)
    (P₀ : CochainComplex (Mod.{c, v, r} J R) ℤ) :
    S.adjunction.unit.app (DerivedCategory.Q.obj P₀) ≫
      (res φ).mapDerivedCategory.map (S.model.ε.app P₀) ≫
      (res φ).mapDerivedCategoryFactors.hom.app
        ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P₀) =
      DerivedCategory.Q.map
        ((S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P₀) := by
  let EC := S.model.E.mapHomologicalComplex (.up ℤ)
  let GC := (res φ).mapHomologicalComplex (.up ℤ)
  let α : DerivedCategory.Q ⟶ EC ⋙ GC ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q S.adjunction.unit ≫
      Functor.whiskerRight S.model.ε (res φ).mapDerivedCategory ≫
      Functor.whiskerLeft EC (res φ).mapDerivedCategoryFactors.hom
  let β : DerivedCategory.Q ⟶ EC ⋙ GC ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit
      DerivedCategory.Q
  change α.app P₀ = β.app P₀
  obtain ⟨P, f, hp, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
  let : IsIso (DerivedCategory.Q.map f) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
  apply (cancel_epi (DerivedCategory.Q.map f)).mp
  rw [α.naturality, β.naturality]
  have hf : α.app P = β.app P := unit_model_flat S P hp
  rw [hf]

private theorem derived_unit_flat (S : ScalarData.{c, v, r} φ)
    (P : CochainComplex (Mod.{c, v, r} J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    S.adjunction.unit.app (DerivedCategory.Q.obj P) =
      (SheafOfModules.sheafScalarDerivedAdjunction φ S.model).unit.app
        (DerivedCategory.Q.obj P) := by
  have ht := unit_model_flat S P hp
  have hc := SheafOfModules.scalar_derived_unit φ S.model P hp
  have hu := ordinary_unit_eq S
  have ha : S.ordinaryAdjunction =
      SheafOfModules.sheafScalarOrdinaryAdjunction φ S.model := Adjunction.ext hu
  have hm : (S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit =
      ((SheafOfModules.sheafScalarOrdinaryAdjunction φ S.model).mapHomologicalComplex
        (.up ℤ)).unit := by rw [ha]
  have : IsIso (S.model.ε.app P) := S.model.computes P hp
  apply (cancel_mono ((res φ).mapDerivedCategory.map (S.model.ε.app P) ≫
    (res φ).mapDerivedCategoryFactors.hom.app
      ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P))).1
  rw [hc, ← hm]
  exact ht

private theorem derived_unit_eq (S : ScalarData.{c, v, r} φ) :
    S.adjunction.unit = (SheafOfModules.sheafScalarDerivedAdjunction φ S.model).unit := by
  ext K
  let P₀ := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨P, f, hp, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
  let : IsIso (DerivedCategory.Q.map f) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
  let e' := asIso (DerivedCategory.Q.map f) ≪≫ e
  apply (cancel_epi e'.hom).mp
  calc
    _ = S.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (S.model.T ⋙ (res φ).mapDerivedCategory).map e'.hom := by
      simpa only [Functor.id_map] using S.adjunction.unit.naturality e'.hom
    _ = _ := by rw [derived_unit_flat S P hp]
    _ = _ := by
      simpa only [Functor.id_map] using
        ((SheafOfModules.sheafScalarDerivedAdjunction φ S.model).unit.naturality e'.hom).symm
/-- The specified scalar adjunction is the normalized canonical adjunction. -/
theorem ScalarData.adjunction_eq (S : ScalarData.{c, v, r} φ) :
    S.adjunction = SheafOfModules.sheafScalarDerivedAdjunction φ S.model :=
  Adjunction.ext (derived_unit_eq S)
end WeilConjectures.SemilinearSections
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
