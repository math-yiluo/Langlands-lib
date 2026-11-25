/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
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
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
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
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.InternalSectionTotalComparison

/-! # Canonical internal-to-sectionwise total-complex comparison

## Main definitions

* `totalComparison`: the fixed comparison of the concrete sum-total complexes.

## References

* Stacks Project, Tags 08J9, 08JA and 08JB
* Stacks 03EK, 06YL
* Stacks 06YS
* Stacks 05RU
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

section GenericComparisonAPI


attribute [local instance 1000001] sectionRingHasSheafCompose

attribute [local implicit_reducible] sectionModuleEquivalence
attribute [local irreducible] sectionRingSheaf
  SheafOfModules.monoidalCategory Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct CategoryTheory.Mod.monoidalClosed
attribute [local implicit_reducible] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Monoidal.induced
attribute [local implicit_reducible] GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory

attribute [local implicit_reducible] Sheaf.symmetricCategory Sheaf.braidedCategory

section TotalData

variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  [MonoidalCategory A] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  (F : A ⥤ B) [F.Additive] [F.IsEquivalence]
  (e : ∀ M N : A, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
  (P Q : CochainComplex A ℤ) [P.HasMapBifunctor Q (curriedTensor A)]
  [CochainComplex.HasMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor B)]

/-- A total comparison together with its complete summand normalization.
For an equivalence F, the images of the total summand inclusions are jointly epic,
so the normalization determines the isomorphism, and all other fields are proofs. -/
structure SectionTensorTotalData where
  iso : (F.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor P Q (curriedTensor A)) ≅
    CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor B)
  summand : ∀ (p q n : ℤ) (h : p + q = n),
    F.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q n h) ≫ iso.hom.f n =
      (e (P.X p) (Q.X q)).hom ≫ CochainComplex.ιMapBifunctor
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor B) p q n h

/-- The normalized total data is unique. -/
theorem SectionTensorTotalData.unique (s t : SectionTensorTotalData F e P Q) : s = t := by
  cases s with
  | mk a ha =>
    cases t with
    | mk b hb =>
      have h : a = b := by
        apply Iso.ext
        ext n : 1
        apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
        intro p q h
        exact (ha p q n h).trans (hb p q n h).symm
      cases h
      rfl

end TotalData

section OrdinaryAtSite

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

attribute [local instance 30001] Sheaf.monoidalCategory

attribute [local instance 30000] sectionComparisonBraiding

variable (R : Sheaf J AddCommGrpCat.{u + 1}) [MonObj R] [hcomm : IsCommMonObj R]


attribute [local instance] sectionRingCommDirect



attribute [local instance] sectionFunctorAdditiveForSite sectionFunctorEquivalenceForSite

/-- The uniquely pure-tensor-normalized ordinary comparison at the generic site.
Construct the coequalizer comparison and then the tensor-sheafification isomorphism.
The formula on local pure tensors determines this data uniquely. -/
@[irreducible]
def ordinaryTensorIsoForSite (M N : Mod (Sheaf J AddCommGrpCat.{u + 1}) R) :
    (sectionModuleFunctor.{u + 1, u + 1, u} J R).obj (M ⊗ N) ≅
      (sectionModuleFunctor.{u + 1, u + 1, u} J R).obj M ⊗
        (sectionModuleFunctor.{u + 1, u + 1, u} J R).obj N :=
  (exists_sectionTensorIso J R M N).choose ≪≫
    (SheafOfModules.tensorObjIsoSheafification
      ((sectionModuleFunctor.{u + 1, u + 1, u} J R).obj M)
      ((sectionModuleFunctor.{u + 1, u + 1, u} J R).obj N)).symm

/-- The ordinary generic map has exactly the prescribed value on every local pure tensor. -/
theorem ordinaryTensorIsoForSite_tmul
    (M N : Mod (Sheaf J AddCommGrpCat.{u + 1}) R) (U : Cᵒᵖ)
    (x : M.X.obj.obj U) (y : N.X.obj.obj U) :
    ((ordinaryTensorIsoForSite J R M N).hom.val.app U)
        (comparison_internalTmul J R M N U x y) =
      comparison_sectionTmul J R
        ((sectionModuleFunctor.{u + 1, u + 1, u} J R).obj M)
        ((sectionModuleFunctor.{u + 1, u + 1, u} J R).obj N) U x y := by
  unfold ordinaryTensorIsoForSite
  exact comparison_tensorIso_tmul J R M N U x y

/-- Both choices have the same formula on every local pure tensor, so relative-tensor
extensionality identifies them. This certifies that the definition repair preserves
all normalized comparison data, not only the isomorphism's existence. -/
private theorem ordinaryTensorIsoForSite_eq_previous
    (M N : Mod (Sheaf J AddCommGrpCat.{u + 1}) R) :
    ordinaryTensorIsoForSite J R M N =
      (internal_section_tensor_comparison J R).2.choose M N := by
  apply Iso.ext
  apply comparison_internalTensor_hom_ext J R M N
  intro U x y
  exact (ordinaryTensorIsoForSite_tmul J R M N U x y).trans
    ((internal_section_tensor_comparison J R).2.choose_spec.choose_spec.1
      M N U x y).symm

attribute [local irreducible] sectionModuleFunctor

/-- The uniquely summand-normalized total comparison before specializing the coefficient. -/
theorem ordinaryTensorIsoForSite_total
    (P Q : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u + 1}) R) ℤ) :
    Nonempty (SectionTensorTotalData (sectionModuleFunctor.{u + 1, u + 1, u} J R)
      (ordinaryTensorIsoForSite J R) P Q) := by
  obtain ⟨t, ht⟩ := (internal_section_tensor_comparison J R).2.choose_spec.choose_spec
    |>.2.2.2.2.2.2.2.1 P Q
  refine ⟨⟨t, ?_⟩⟩
  intro p q n h
  exact (ht p q n h).trans (congrArg (fun e ↦ e.hom ≫
    CochainComplex.ιMapBifunctor
      (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex (.up ℤ)).obj P)
      (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor _) p q n h)
        (ordinaryTensorIsoForSite_eq_previous J R (P.X p) (Q.X q)).symm)

/-- The fixed total map, chosen at the generic site before any coefficient specialization.
Its summand formula uniquely determines it, so this is normalized comparison data. -/
@[irreducible]
def ordinaryComplexTensorIsoForSite
    (P Q : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u + 1}) R) ℤ) :
    ((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor _)) ≅
      CochainComplex.mapBifunctor
        (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex (.up ℤ)).obj P)
        (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor _) :=
  (Classical.choice (ordinaryTensorIsoForSite_total J R P Q)).iso

/-- The generic total map retains every normalized summand equation. -/
theorem ordinaryComplexTensorIsoForSite_summand
    (P Q : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u + 1}) R) ℤ) :
    ∀ (p q n : ℤ) (h : p + q = n),
        (sectionModuleFunctor.{u + 1, u + 1, u} J R).map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫
            (ordinaryComplexTensorIsoForSite J R P Q).hom.f n =
        (ordinaryTensorIsoForSite J R (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor
            (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex (.up ℤ)).obj P)
            (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex (.up ℤ)).obj Q)
            (curriedTensor _) p q n h := by
  unfold ordinaryComplexTensorIsoForSite
  exact (Classical.choice (ordinaryTensorIsoForSite_total J R P Q)).summand

end OrdinaryAtSite

end GenericComparisonAPI

section ProEtaleComparisonAPI

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})


end ProEtaleComparisonAPI

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})


attribute [instance 1000001] coefficientMonoid














/-- The ordinary lax localization comparison, for the same total tensor. -/
def localizationTensorMap (P Q : CochainComplex (Internal Λ X) ℤ) :
    ((CondensedRing.derivedTensor Λ X).obj ((DerivedCategory.Q (C := Internal Λ X)).obj P)).obj
      ((DerivedCategory.Q (C := Internal Λ X)).obj Q) ⟶
      (DerivedCategory.Q (C := Internal Λ X)).obj (internalTotalTensor Λ X P Q) := by
  letI := internalComplexMonoidal Λ X
  exact Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Internal Λ X)) P Q

/-- Its termwise extension to ordinary unbounded derived categories. -/
def forward : DerivedCategory (Internal Λ X) ⥤ DerivedCategory (Modules Λ X) :=
  (sectionForward Λ X).mapDerivedCategory



/-- The actual localization comparison for the termwise equivalence. -/
def localizationIso : DerivedCategory.Q ⋙ forward Λ X ≅
    complexForward Λ X ⋙ DerivedCategory.Q :=
  (sectionForward Λ X).mapDerivedCategoryFactors

attribute [local instance 1000001] sectionRingHasSheafCompose

attribute [local implicit_reducible] sectionModuleEquivalence
attribute [local irreducible] sectionRingSheaf
  SheafOfModules.monoidalCategory Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct CategoryTheory.Mod.monoidalClosed
attribute [local implicit_reducible] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Monoidal.induced
attribute [local implicit_reducible] GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory

attribute [local implicit_reducible] Sheaf.symmetricCategory Sheaf.braidedCategory

/-- The ordinary sectionwise tensor bifunctor, with its coefficient ring fixed. -/
abbrev sectionTensor : Modules Λ X ⥤ Modules Λ X ⥤ Modules Λ X :=
  @curriedTensor (Modules Λ X) _ (SheafOfModules.monoidalCategory (ring Λ X))

/-- The dependency's ordinary tensor comparison, fixed by its pure-tensor formula. -/
def ordinaryTensorIso (M N : Internal Λ X) :
    (equivalence Λ X).functor.obj (M ⊗ N) ≅
      ((sectionTensor Λ X).obj ((equivalence Λ X).functor.obj M)).obj
        ((equivalence Λ X).functor.obj N) :=
  ordinaryTensorIsoForSite (hcomm := isCommMonObj_condensedRingObj Λ X)
    (Scheme.ProEt.topology X) (condensedRingObj Λ X) M N

/-- The existing total-complex comparison, pinned on every summand by the
ordinary tensor comparison and hence on every local pure tensor. -/
def complexTensorIso (P Q : CochainComplex (Internal Λ X) ℤ) :
    (complexForward Λ X).obj
      (CochainComplex.mapBifunctor P Q (curriedTensor (Internal Λ X))) ≅
    CochainComplex.mapBifunctor ((complexForward Λ X).obj P)
      ((complexForward Λ X).obj Q) (sectionTensor Λ X) :=
  ordinaryComplexTensorIsoForSite (hcomm := isCommMonObj_condensedRingObj Λ X)
    (Scheme.ProEt.topology X) (condensedRingObj Λ X) P Q

attribute [local irreducible] ordinaryTensorIso

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
