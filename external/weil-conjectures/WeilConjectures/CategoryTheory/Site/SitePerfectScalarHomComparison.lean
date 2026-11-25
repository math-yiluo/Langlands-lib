/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
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
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeTensor
import WeilConjectures.CategoryTheory.Ringed.RingedScalarTensorMonoidal
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison

/-! # Evaluation-normalized scalar Hom comparison for a site-perfect source

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, lemma-dual-perfect-complex;
current blueprint lem-fix-operation-reduction.proof.md, paragraph 1.
(blueprint: lem-fix-site-perfect-scalar-hom).

The auxiliary data retain the existing scalar universal pair, fixed K-flat tensor
models, and Koszul symmetry. The comparison is constructed by the specified transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
attribute [local irreducible] SheafOfModules.monoidalCategory derivedInternalHomOfUniverses

namespace CategoryTheory

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J S)]

/-- The canonical ordinary scalar tensor formula on pure generators, before localization.
Source: Stacks 07A4; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def SiteScalarHomGeneratorFormula
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ)
    (κ : coefficientTotalTensor.{r, c, v} J R ⋙ D.E.mapHomologicalComplex (.up ℤ) ≅
      (D.E.mapHomologicalComplex (.up ℤ)).prod (D.E.mapHomologicalComplex (.up ℤ)) ⋙
        coefficientTotalTensor.{r, c, v} J S) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
      (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      ((κ.hom.app (P, Q)).f (p + q)).val.app U
        (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq
          (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
          U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
            P Q p q (p + q) rfl U x y)) =
      WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
        ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
        (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (P.X p) U 1 x)
        (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (Q.X q) U 1 y)

/-- The canonical derived tensor comparison is fixed by its K-flat counit square.
This is the same representative characterization as ringed-topos tensor pullback.
Source: Stacks 07A4; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def SiteScalarHomTensorNormalization
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ)
    (AR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (AS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (MR : CoefficientTensorModels.{r, c, v, w} J R AR)
    (MS : CoefficientTensorModels.{r, c, v, w} J S AS)
    (κ : coefficientTotalTensor.{r, c, v} J R ⋙ D.E.mapHomologicalComplex (.up ℤ) ≅
      (D.E.mapHomologicalComplex (.up ℤ)).prod (D.E.mapHomologicalComplex (.up ℤ)) ⋙
        coefficientTotalTensor.{r, c, v} J S)
    (μ : AR.tensor ⋙ D.T ≅ D.T.prod D.T ⋙ AS.tensor) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
      ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
        D.T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
            μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            AS.tensor.map (Prod.mkHom (D.ε.app P) (D.ε.app Q)) =
          D.ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
            DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
            (MS.iso J S AS _ _ hEP hEQ).hom

attribute [local irreducible] SiteScalarHomGeneratorFormula SiteScalarHomTensorNormalization

/-- A presentation of the actual scalar and tensor operations used in the Hom map.
The final two fields are exactly the canonical pure-tensor and K-flat counit squares
of the published scalar tensor comparison, with no finite-free hypothesis on S.
These data are existential conclusions of the main theorem, not extra hypotheses.
Source: Stacks 07A4, 08J9 and 08JJ; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
structure SitePerfectScalarHomData where
  /-- The existing universal derived change of rings, with actual ordinary extension. -/
  scalar : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ
  /-- The closed structure with the fixed derived internal Hom over R. -/
  sourceClosed : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- The closed structure with the fixed derived internal Hom over S. -/
  targetClosed : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S)
  /-- Its actual K-flat tensor and Hom-evaluation normalization over R. -/
  sourceModel : CoefficientTensorModels.{r, c, v, w} J R sourceClosed
  /-- Its actual K-flat tensor and Hom-evaluation normalization over S. -/
  targetModel : CoefficientTensorModels.{r, c, v, w} J S targetClosed
  /-- The symmetry over R. -/
  sourceSymmetry : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ sourceClosed.monoidal
  /-- The symmetry over S. -/
  targetSymmetry : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J S))
    _ targetClosed.monoidal
  /-- The source symmetry is the Koszul symmetry and its unit is R in degree zero. -/
  sourceCoherence : RingedDerivedTensorCoherence.{c, v, r, w} J R
    sourceClosed sourceModel sourceSymmetry
  /-- The target symmetry is the Koszul symmetry and its unit is S in degree zero. -/
  targetCoherence : RingedDerivedTensorCoherence.{c, v, r, w} J S
    targetClosed targetModel targetSymmetry
  /-- The ordinary total-tensor scalar comparison. -/
  complexIso : coefficientTotalTensor.{r, c, v} J R ⋙
      scalar.E.mapHomologicalComplex (.up ℤ) ≅
    (scalar.E.mapHomologicalComplex (.up ℤ)).prod
      (scalar.E.mapHomologicalComplex (.up ℤ)) ⋙ coefficientTotalTensor.{r, c, v} J S
  /-- The derived comparison t: F(P tensor Q) = FP tensor FQ. -/
  tensorIso : sourceClosed.tensor ⋙ scalar.T ≅ scalar.T.prod scalar.T ⋙ targetClosed.tensor
  /-- The ordinary comparison is fixed on sheafified pure tensor generators. -/
  generators : SiteScalarHomGeneratorFormula J φ scalar complexIso
  /-- The derived comparison is the localization of this same chain comparison. -/
  normalization : SiteScalarHomTensorNormalization J φ scalar sourceClosed targetClosed
    sourceModel targetModel complexIso tensorIso

variable (M : SitePerfectScalarHomData.{c, v, r, w} J φ)

end Site

end CategoryTheory
