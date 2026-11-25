/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Strict scalar identification of unbounded product Hom complexes

Source: Stacks Project, sites-modules.tex, Tags 03CZ, 03CY and 03EL;
sites-cohomology.tex, Tag 0A8X. The extension to the strict chain square and
coefficient compatibility is the agent argument recorded in the DAG.
(blueprint: lem-sfb-hom-scalar-chain-identification).

The structures below package the normalized maps and their equations. Their
simultaneous existence is constructed from the scalar adjunction and the actual
Hom products. All evaluations use the chosen projections and slice identity.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace SheafOfModules.StrictScalarHom

private theorem pointFromExtend_tmul {A B : CommRingCat.{u}}
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) (f : A ⟶ B)
    (g : M ⟶ (ModuleCat.restrictScalars f.hom).obj N) (s : B) (x : M) :
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f.hom g
        (s ⊗ₜ[A, f.hom] x) = s • (show N from g x) := by
  let : Module A B := Module.compHom B f.hom
  let : Module A N := Module.compHom N f.hom
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  rfl

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}]

/-- Transparent notation for the existing unbounded module complexes.
Source: Stacks 0A8X (blueprint: lem-sfb-hom-scalar-chain-identification). -/
abbrev Complex (R : Sheaf J CommRingCat.{max c v u}) :=
  CochainComplex (ringedSiteModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ

/-- Termwise Mathlib restriction of scalars.
Source: Stacks 03CZ (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def restriction {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    Complex.{c, v, u} S ⥤ Complex.{c, v, u} R :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
    (.up ℤ)

/-- The fixed R-module S, obtained by restricting the unit S-module.
Source: Stacks 03CZ (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def scalarModule {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))

/-- The ordinary R-linear tensor S tensor A, applied termwise, using the existing tensor.
Source: Stacks 03EK (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def tensor {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    Complex.{c, v, u} R ⥤ Complex.{c, v, u} R :=
  (tensorLeft (scalarModule.{c, v, u} φ)).mapHomologicalComplex (.up ℤ)

/-- The sheafification-unit image of s tensor x in the R-linear tensor.
Source: Stacks 03CY, 03EK (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def tensorSection {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (s : S.obj.obj V) (x : (A.X n).val.obj V) :
    (((tensor.{c, v, u} φ).obj A).X n).val.obj V :=
  (tensorObjIsoSheafification (scalarModule.{c, v, u} φ) (A.X n)).inv.val.app V
    (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      ((scalarModule.{c, v, u} φ).val ⊗ (A.X n).val)).app V (s ⊗ₜ[R.obj.obj V] x))

/-- Actual local evaluation, using the chosen product projection and slice identity.
Source: Stacks 0A8X; the convention of def-coef-hom-representative-evaluation
(blueprint: lem-sfb-hom-scalar-chain-identification). -/
def evaluate {R : Sheaf J CommRingCat.{max c v u}} (P N : Complex.{c, v, u} R)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (g : ((homComplex (R := R) P N).X n).val.obj V)
    (x : (P.X i).val.obj V) : (N.X k).val.obj V :=
  (((homComplexπ (R := R) P N n i k h).val.app V g).app
    (op (Over.mk (𝟙 V.unop)))).hom x

/-- The existing componentwise action of the actual product Hom bifunctor.
Source: Stacks 0A8X (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def homMap {R : Sheaf J CommRingCat.{max c v u}}
    {P P' N N' : Complex.{c, v, u} R} (a : P' ⟶ P) (b : N ⟶ N') :
    homComplex (R := R) P N ⟶ homComplex (R := R) P' N' :=
  (homComplexFunctor.map a.op).app N ≫ (homComplexFunctor.obj (op P')).map b

/-- Ordinary scalar extension with its object and map functions pinned to the existing
sheafification construction. Additivity permits termwise application.
Source: Stacks 03CZ, 03CY (blueprint: lem-sfb-hom-scalar-chain-identification). -/
structure Extension {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) where
  /-- The ordinary module functor. -/
  functor : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
    ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  /-- Exactly the sheafified ordinary scalar extension on objects. -/
  obj_eq : ∀ M, functor.obj M = changeOfRingsOfUniverses φ M
  /-- Exactly the sheafified map id tensor f on morphisms. -/
  map_eq : ∀ {M N} (f : M ⟶ N), functor.map f =
    eqToHom (obj_eq M) ≫ changeOfRingsHomOfUniverses φ M f ≫ eqToHom (obj_eq N).symm
  /-- Ordinary extension is additive. -/
  [additive : functor.Additive]

attribute [instance] Extension.additive

/-- The termwise functor associated to ordinary extension.
Source: Stacks 03CZ, 0A8X (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def Extension.complex {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : Complex.{c, v, u} R ⥤ Complex.{c, v, u} S :=
  E.functor.mapHomologicalComplex (.up ℤ)

/-- Pure sections transported by the explicit object equality, with no arbitrary map.
Source: Stacks 03CY (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def Extension.section {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (A.X n).val.obj V) :
    ((E.complex.obj A).X n).val.obj V :=
  (eqToHom (E.obj_eq (A.X n)).symm).val.app V
    (scalarExtensionSection φ (A.X n) V s x)

/-- The normalization predicate for the S-linear evaluation map.
Source: Stacks 03CZ, 0A8X (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def SigmaFormula {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : E.complex.obj A ⟶ N)
    (σ : E.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (E.complex.obj P) N) : Prop :=
  ∀ (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ) (s t : S.obj.obj V)
    (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V),
    evaluate.{c, v, u} (E.complex.obj P) N n i k h V
        ((σ.f n).val.app V (E.section (homComplex (R := R) P A) n V s f))
        (E.section P i V t x) =
      (s * t) • (q.f k).val.app V (E.section A k V 1 (evaluate.{c, v, u} P A n i k h V f x))

/-- All normalized chain maps for one coefficient morphism, with their strict square
and input naturality. No boundedness, flatness, or resolution is part of this data.
Source: Stacks 03CZ, 03CY and 0A8X
(blueprint: lem-sfb-hom-scalar-chain-identification). -/
structure Data {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) where
  /-- The actual ordinary extension. -/
  extension : Extension.{c, v, u} φ
  /-- The identity-on-generators natural chain isomorphism. -/
  nu : tensor.{c, v, u} φ ≅ extension.complex ⋙ restriction.{c, v, u} φ
  /-- Its generator normalization in every degree and over every object. -/
  nu_pure : ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((nu.app A).hom.f n).val.app V) (tensorSection.{c, v, u} φ A n V s x) =
      extension.section A n V s x
  /-- The actual product-Hom chain isomorphism. -/
  theta : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S),
    (restriction.{c, v, u} φ).obj (homComplex (R := S) (extension.complex.obj P) N) ≅
      homComplex (R := R) P ((restriction.{c, v, u} φ).obj N)
  /-- Its formula uses the actual local product projection. -/
  theta_evaluate : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (g : ((homComplex (R := S) (extension.complex.obj P) N).X n).val.obj V)
    (x : (P.X i).val.obj V),
    evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) n i k h V
        ((((theta P N).hom.f n).val.app V) g) x =
      evaluate.{c, v, u} (extension.complex.obj P) N n i k h V g (extension.section P i V 1 x)
  /-- The R-linear scalar-Hom comparison, with no product-preservation assertion. -/
  alpha : ∀ (P A : Complex.{c, v, u} R),
    (tensor.{c, v, u} φ).obj (homComplex (R := R) P A) ⟶
      homComplex (R := R) P ((tensor.{c, v, u} φ).obj A)
  /-- Alpha is s tensor f evaluated at x equals s tensor f(x). -/
  alpha_evaluate : ∀ (P A : Complex.{c, v, u} R) (n i k : ℤ) (h : i + n = k)
    (V : Cᵒᵖ) (s : S.obj.obj V)
    (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V),
    evaluate.{c, v, u} P ((tensor.{c, v, u} φ).obj A) n i k h V
        (((alpha P A).f n).val.app V
          (tensorSection.{c, v, u} φ (homComplex (R := R) P A) n V s f)) x =
      tensorSection.{c, v, u} φ A k V s (evaluate.{c, v, u} P A n i k h V f x)
  /-- The S-linear scalar evaluation chain map for every q. -/
  sigma : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (_q : extension.complex.obj A ⟶ N),
    extension.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (extension.complex.obj P) N
  /-- The normalized formula on both sets of local generators. -/
  sigma_formula : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : extension.complex.obj A ⟶ N),
    SigmaFormula.{c, v, u} extension P A N q (sigma P A N q)
  /-- Uniqueness among all S-linear chain maps with that formula. -/
  sigma_unique : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : extension.complex.obj A ⟶ N)
    (s : extension.complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) (extension.complex.obj P) N),
    SigmaFormula.{c, v, u} extension P A N q s → s = sigma P A N q
  /-- The asserted equality holds in the category of complexes before localization. -/
  square : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : extension.complex.obj A ⟶ N),
    (nu.app (homComplex (R := R) P A)).hom ≫
        (restriction.{c, v, u} φ).map (sigma P A N q) ≫ (theta P N).hom =
      alpha P A ≫ homMap.{c, v, u} (𝟙 P) (nu.app A).hom ≫
        homMap.{c, v, u} (𝟙 P) ((restriction.{c, v, u} φ).map q)
  /-- Theta is contravariant in P and covariant in N. -/
  theta_natural : ∀ (P P' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
    (a : P' ⟶ P) (w : N ⟶ N'),
    (restriction.{c, v, u} φ).map (homMap.{c, v, u} (extension.complex.map a) w) ≫
        (theta P' N').hom =
      (theta P N).hom ≫ homMap.{c, v, u} a ((restriction.{c, v, u} φ).map w)
  /-- Alpha commutes with chain maps of both inputs. -/
  alpha_natural : ∀ (P P' A A' : Complex.{c, v, u} R) (a : P' ⟶ P) (b : A ⟶ A'),
    (tensor.{c, v, u} φ).map (homMap.{c, v, u} a b) ≫ alpha P' A' =
      alpha P A ≫ homMap.{c, v, u} a ((tensor.{c, v, u} φ).map b)
  /-- Sigma commutes with compatible changes of P, A, N and q. -/
  sigma_natural : ∀ (P P' A A' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
    (q : extension.complex.obj A ⟶ N) (q' : extension.complex.obj A' ⟶ N')
    (a : P' ⟶ P) (b : A ⟶ A') (w : N ⟶ N'),
    extension.complex.map b ≫ q' = q ≫ w →
      extension.complex.map (homMap.{c, v, u} a b) ≫ sigma P' A' N' q' =
        sigma P A N q ≫ homMap.{c, v, u} (extension.complex.map a) w

/-- The canonical extension identification and restriction mate for a commuting
square of coefficient sheaves, both pinned by local tensor generators.
Source: Stacks 03CZ, 03CY (blueprint: lem-sfb-hom-scalar-chain-identification). -/
structure CoefficientSquare
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    (D : Data.{c, v, u} φ) (Da : Data.{c, v, u} a) (Db : Data.{c, v, u} b)
    (D' : Data.{c, v, u} φ') where
  /-- Identify the two iterated ordinary extensions. -/
  extensionIso : D.extension.complex ⋙ Db.extension.complex ≅
    Da.extension.complex ⋙ D'.extension.complex
  /-- The identification multiplies the scalars in the common S'-extension. -/
  extensionIso_pure : ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (t : S'.obj.obj V) (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((extensionIso.app A).hom.f n).val.app V)
        (Db.extension.section (D.extension.complex.obj A) n V t
          (D.extension.section A n V s x)) =
      D'.extension.section (Da.extension.complex.obj A) n V (t * b.hom.app V s)
        (Da.extension.section A n V 1 x)
  /-- Extension of an R-restricted S-complex maps to the R'-restricted S'-extension. -/
  restrictionMate : restriction.{c, v, u} φ ⋙ Da.extension.complex ⟶
    Db.extension.complex ⋙ restriction.{c, v, u} φ'
  /-- The mate sends r' tensor z to phi'(r') tensor z. -/
  restrictionMate_pure : ∀ (N : Complex.{c, v, u} S) (n : ℤ) (V : Cᵒᵖ)
    (r : R'.obj.obj V) (z : (N.X n).val.obj V),
    (((restrictionMate.app N).f n).val.app V)
        (Da.extension.section ((restriction.{c, v, u} φ).obj N) n V r z) =
      Db.extension.section N n V (φ'.hom.app V r) z

/-- The canonical coefficient map on S tensor A, transported through the normalized
nu maps and the generator-normalized mate. It need not be an isomorphism.
Source: Stacks 03CZ, 03EK (blueprint: lem-sfb-hom-scalar-chain-identification). -/
def CoefficientSquare.tensorComparison
    {R S R' S' : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} {a : R ⟶ R'} {b : S ⟶ S'} {φ' : R' ⟶ S'}
    {D : Data.{c, v, u} φ} {Da : Data.{c, v, u} a} {Db : Data.{c, v, u} b} {D' : Data.{c, v, u} φ'}
    (Q : CoefficientSquare.{c, v, u} D Da Db D') (A : Complex.{c, v, u} R) :
    Da.extension.complex.obj ((tensor.{c, v, u} φ).obj A) ⟶
      (tensor.{c, v, u} φ').obj (Da.extension.complex.obj A) :=
  Da.extension.complex.map (D.nu.app A).hom ≫
    Q.restrictionMate.app (D.extension.complex.obj A) ≫
    (restriction.{c, v, u} φ').map (Q.extensionIso.app A).hom ≫
    (D'.nu.app (Da.extension.complex.obj A)).inv

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

private theorem evaluate_homMap {R : Sheaf J CommRingCat.{max c v u}}
    {P P' N N' : Complex.{c, v, u} R} (a : P' ⟶ P) (b : N ⟶ N')
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (f : ((homComplex (R := R) P N).X n).val.obj V)
    (x : (P'.X i).val.obj V) :
    evaluate.{c, v, u} (R := R) P' N' n i k h V (((homMap.{c, v, u} (R := R) a b).f n).val.app V f)
      x =
      (b.f k).val.app V (evaluate.{c, v, u} (R := R) P N n i k h V f ((a.f i).val.app V x)) := by
  have he := homComplexFunctor_map_f_π (R := R) a b n i k h
  have hh := congrArg
    (fun z : (homComplex (R := R) P N).X n ⟶
      homObj (R := R) (P'.X i) (N'.X k) ↦
        ((z.val.app V f).app (op (Over.mk (𝟙 V.unop)))).hom x) he
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app] at hh
  erw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hh
  exact hh

private theorem evaluate_hom_ext {R : Sheaf J CommRingCat.{max c v u}}
    (P N : Complex.{c, v, u} R) (n : ℤ)
    {H : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (a b : H ⟶ (homComplex (R := R) P N).X n)
    (h : ∀ (i k : ℤ) (hik : i + n = k) (V : Cᵒᵖ)
      (z : H.val.obj V) (x : (P.X i).val.obj V),
      evaluate.{c, v, u} (R := R) P N n i k hik V (a.val.app V z) x =
        evaluate.{c, v, u} (R := R) P N n i k hik V (b.val.app V z) x) : a = b := by
  apply homComplex_hom_ext (R := R)
  intro i k hik
  let a' := a ≫ homComplexπ (R := R) P N n i k hik
  let b' := b ≫ homComplexπ (R := R) P N n i k hik
  change a' = b'
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hh := h i k hik (op W.unop.left) (H.val.map W.unop.hom.op z) x
  change (a'.val.app (op W.unop.left) (H.val.map W.unop.hom.op z)).app
      (op (Over.mk (𝟙 W.unop.left))) x =
    (b'.val.app (op W.unop.left) (H.val.map W.unop.hom.op z)).app
      (op (Over.mk (𝟙 W.unop.left))) x at hh
  rw [PresheafOfModules.naturality_apply a'.val,
    PresheafOfModules.naturality_apply b'.val] at hh
  change (a'.val.app V z).app (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom))) x =
    (b'.val.app V z).app (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom))) x at hh
  exact (PresheafOfModules.restrictOver_hom_app_congr (a'.val.app V z)
    (Category.id_comp W.unop.hom) x).symm.trans
      (hh.trans (PresheafOfModules.restrictOver_hom_app_congr (b'.val.app V z)
        (Category.id_comp W.unop.hom) x))

attribute [local irreducible] homComplexFunctor

private def ordinaryExtension {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    ringedSiteModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) where
  obj M := changeOfRingsOfUniverses φ M
  map f := changeOfRingsHomOfUniverses φ _ f
  map_id M := scalarExtension_map_id φ M
  map_comp f g := scalarExtension_map_comp φ f g

private theorem ordinaryExtension_additive
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    (ordinaryExtension.{c, v, u} φ).Additive where
  map_add {M N} f g := by
    change changeOfRingsHomOfUniverses φ M (f + g) =
      changeOfRingsHomOfUniverses φ M f + changeOfRingsHomOfUniverses φ M g
    apply scalarExtension_hom_ext φ M
    intro V s x
    simp only [scalarExtension_map_tmul, add_val, PresheafOfModules.add_app,
      ModuleCat.hom_add, LinearMap.add_apply]
    exact scalarExtensionSection_add φ N V s _ _

attribute [local instance] ordinaryExtension_additive

private def canonicalExtension {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    Extension.{c, v, u} φ where
  functor := ordinaryExtension.{c, v, u} φ
  obj_eq _ := rfl
  map_eq _ := by simp [ordinaryExtension]

private abbrev moduleRestriction {R S : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) :
    ringedSiteModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⥤
      ringedSiteModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

private def tensorToRestriction {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (f : changeOfRingsPresheafOfUniverses φ M ⟶ N.val) :
    M ⟶ (moduleRestriction.{c, v, u} φ).obj N where
  val :=
    { app := fun V ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (φ.hom.app V).hom (f.app V)
      naturality := by
        intro V W i
        ext x
        change f.app W ((1 : S.obj.obj W) ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom]
          M.val.map i x) = N.val.map i (f.app V
            ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)
        erw [changeOfRingsMap_tmulOfUniverses, map_one] at h
        exact h }

private def restrictionToTensor {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (g : M ⟶ (moduleRestriction.{c, v, u} φ).obj N) :
    changeOfRingsPresheafOfUniverses φ M ⟶ N.val where
  app V := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (φ.hom.app V).hom (g.val.app V)
  naturality := by
    intro V W i
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    have h := PresheafOfModules.naturality_apply g.val i x
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (φ.hom.app W).hom (g.val.app W)
        ((changeOfRingsPresheafOfUniverses φ M).map i
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)) =
      N.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (φ.hom.app V).hom (g.val.app V)
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x))
    erw [changeOfRingsMap_tmulOfUniverses, map_one]
    have atOne (U : Cᵒᵖ) (m : M.val.obj U) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (φ.hom.app U).hom (g.val.app U)
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) =
          g.val.app U m := by
      exact congrArg (fun f : M.val.obj U ⟶
        (ModuleCat.restrictScalars (φ.hom.app U).hom).obj (N.val.obj U) ↦ f m)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (φ.hom.app U).hom).apply_symm_apply
          (g.val.app U))
    rw [atOne, atOne]
    exact h

private def scalarPresheafHomEquiv {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :
    (changeOfRingsPresheafOfUniverses φ M ⟶ N.val) ≃
      (M ⟶ (moduleRestriction.{c, v, u} φ).obj N) where
  toFun := tensorToRestriction.{c, v, u} φ M N
  invFun := restrictionToTensor.{c, v, u} φ M N
  left_inv f := by
    ext V : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (φ.hom.app V).hom).symm_apply_apply
      (f.app V)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext V : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (φ.hom.app V).hom).apply_symm_apply
      (g.val.app V)

private def scalarSheafHomEquiv {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :
    (changeOfRingsOfUniverses φ M ⟶ N) ≃ (M ⟶ (moduleRestriction.{c, v, u} φ).obj N) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv _ _).trans
      (scalarPresheafHomEquiv.{c, v, u} φ M N)

private theorem scalarSheafHomEquiv_apply
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (f : changeOfRingsOfUniverses φ M ⟶ N) (V : Cᵒᵖ) (x : M.val.obj V) :
    (scalarSheafHomEquiv.{c, v, u} φ M N f).val.app V x =
      f.val.app V (scalarExtensionSection φ M V 1 x) := by
  rfl

private theorem scalarSheafHomEquiv_natural_left
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    {M M' : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (a : M' ⟶ M)
    (N : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (f : changeOfRingsOfUniverses φ M ⟶ N) :
    scalarSheafHomEquiv.{c, v, u} φ M' N ((ordinaryExtension.{c, v, u} φ).map a ≫ f) =
      a ≫ scalarSheafHomEquiv.{c, v, u} φ M N f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext x
  rw [scalarSheafHomEquiv_apply.{c, v, u}]
  change f.val.app V
    ((changeOfRingsHomOfUniverses φ M' a).val.app V
      (scalarExtensionSection φ M' V 1 x)) =
    (scalarSheafHomEquiv.{c, v, u} φ M N f).val.app V (a.val.app V x)
  rw [scalarExtension_map_tmul, scalarSheafHomEquiv_apply.{c, v, u}]

private theorem scalarSheafHomEquiv_natural_right
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {N N' : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)}
    (f : changeOfRingsOfUniverses φ M ⟶ N) (b : N ⟶ N') :
    scalarSheafHomEquiv.{c, v, u} φ M N' (f ≫ b) =
      scalarSheafHomEquiv.{c, v, u} φ M N f ≫ (moduleRestriction.{c, v, u} φ).map b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext x
  rw [scalarSheafHomEquiv_apply.{c, v, u}]
  change b.val.app V (f.val.app V (scalarExtensionSection φ M V 1 x)) =
    b.val.app V ((scalarSheafHomEquiv.{c, v, u} φ M N f).val.app V x)
  rw [scalarSheafHomEquiv_apply.{c, v, u}]

attribute [local irreducible] scalarSheafHomEquiv

private def ordinaryAdjunction {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    ordinaryExtension.{c, v, u} φ ⊣ moduleRestriction.{c, v, u} φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := scalarSheafHomEquiv.{c, v, u} φ
      homEquiv_naturality_left_symm := by
        intro M M' N a g
        apply (scalarSheafHomEquiv.{c, v, u} φ M N).injective
        erw [Equiv.apply_symm_apply, scalarSheafHomEquiv_natural_left.{c, v, u},
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ scalarSheafHomEquiv_natural_right.{c, v, u} φ _ f b }

attribute [local irreducible] ordinaryAdjunction

private abbrev Mod (R : Sheaf J CommRingCat.{max c v u}) :=
  ringedSiteModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

private def tensorUnit {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) (M : Mod.{c, v, u} R) :
    changeOfRingsPresheafOfUniverses φ M ⟶ (changeOfRingsOfUniverses φ M).val :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app _

private theorem tensorUnit_locallyInjective
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) (M : Mod.{c, v, u} R) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (tensorUnit.{c, v, u} φ M)) := by
  change Presheaf.IsLocallyInjective J
    (toSheafify J (changeOfRingsPresheafOfUniverses φ M).presheaf)
  infer_instance

private theorem tensorUnit_locallySurjective
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) (M : Mod.{c, v, u} R) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (tensorUnit.{c, v, u} φ M)) := by
  change Presheaf.IsLocallySurjective J
    (toSheafify J (changeOfRingsPresheafOfUniverses φ M).presheaf)
  infer_instance

private def localTensorLiftRaw {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (g : (homObj (R := R) M ((moduleRestriction.{c, v, u} φ).obj N)).val.obj V) :
    (PresheafOfModules.restrictOver S.obj V.unop).obj
        (changeOfRingsPresheafOfUniverses φ M) ⟶
      (PresheafOfModules.restrictOver S.obj V.unop).obj N.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (φ.hom.app (op W.unop.left)).hom (g.app W)
  naturality := by
    intro W W' i
    apply ModuleCat.ExtendScalars.hom_ext (f := (φ.hom.app (op W.unop.left)).hom)
    intro x
    have h := PresheafOfModules.naturality_apply g i x
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (φ.hom.app (op W'.unop.left)).hom (g.app W')
        (changeOfRingsMapOfUniverses φ M i.unop.left.op
          ((1 : S.obj.obj (op W.unop.left)) ⊗ₜ[R.obj.obj (op W.unop.left),
            (φ.hom.app (op W.unop.left)).hom] x)) =
      N.val.map i.unop.left.op
        (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (φ.hom.app (op W.unop.left)).hom (g.app W)
            ((1 : S.obj.obj (op W.unop.left)) ⊗ₜ[R.obj.obj (op W.unop.left),
              (φ.hom.app (op W.unop.left)).hom] x))
    erw [changeOfRingsMap_tmulOfUniverses, map_one]
    erw [pointFromExtend_tmul (M.val.obj (op W'.unop.left))
      (N.val.obj (op W'.unop.left)) (φ.hom.app (op W'.unop.left)), one_smul,
      pointFromExtend_tmul (M.val.obj (op W.unop.left))
        (N.val.obj (op W.unop.left)) (φ.hom.app (op W.unop.left)), one_smul]
    exact h

private def localTensorAdjunctionEquiv
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ) :
    ((homObj (R := S) (changeOfRingsOfUniverses φ M) N).val.obj V) ≃
      ((PresheafOfModules.restrictOver S.obj V.unop).obj
          (changeOfRingsPresheafOfUniverses φ M) ⟶
        (PresheafOfModules.restrictOver S.obj V.unop).obj N.val) := by
  have : (J.over V.unop).WEqualsLocallyBijective AddCommGrpCat.{max c v u} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  let η := (PresheafOfModules.restrictOver S.obj V.unop).map (tensorUnit.{c, v, u} φ M)
  have := tensorUnit_locallyInjective.{c, v, u} φ M
  have := tensorUnit_locallySurjective.{c, v, u} φ M
  have : PresheafOfModules.IsLocallyInjective (J.over V.unop) η :=
    Presheaf.isLocallyInjective_whisker (J.over V.unop) J (Over.forget V.unop)
      ((PresheafOfModules.toPresheaf _).map (tensorUnit.{c, v, u} φ M))
  have : PresheafOfModules.IsLocallySurjective (J.over V.unop) η :=
    Presheaf.isLocallySurjective_whisker (J.over V.unop) J (Over.forget V.unop)
      ((PresheafOfModules.toPresheaf _).map (tensorUnit.{c, v, u} φ M))
  exact PresheafOfModules.homEquivOfIsLocallyBijective
    (f := η) (N.over V.unop).isSheaf

private theorem localTensorAdjunctionEquiv_apply
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (f : (homObj (R := S) (changeOfRingsOfUniverses φ M) N).val.obj V)
    (W : (Over V.unop)ᵒᵖ) (s : S.obj.obj (op W.unop.left))
    (x : M.val.obj (op W.unop.left)) :
    ((localTensorAdjunctionEquiv.{c, v, u} φ M N V f).app W)
      (s ⊗ₜ[R.obj.obj (op W.unop.left), (φ.hom.app (op W.unop.left)).hom] x) =
    f.app W (scalarExtensionSection φ M (op W.unop.left) s x) := rfl

attribute [local irreducible] localTensorAdjunctionEquiv

private def localTensorLift {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (g : (homObj (R := R) M ((moduleRestriction.{c, v, u} φ).obj N)).val.obj V) :
    (homObj (R := S) (changeOfRingsOfUniverses φ M) N).val.obj V :=
  (localTensorAdjunctionEquiv.{c, v, u} φ M N V).symm
    (localTensorLiftRaw.{c, v, u} φ M N V g)

private theorem localTensorLift_apply {R S : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (g : (homObj (R := R) M ((moduleRestriction.{c, v, u} φ).obj N)).val.obj V)
    (W : (Over V.unop)ᵒᵖ) (s : S.obj.obj (op W.unop.left))
    (x : M.val.obj (op W.unop.left)) :
    (localTensorLift.{c, v, u} φ M N V g).app W
        (scalarExtensionSection φ M (op W.unop.left) s x) = s • (show N.val.obj (op W.unop.left)
          from g.app W x) := by
  have he := (localTensorAdjunctionEquiv.{c, v, u} φ M N V).apply_symm_apply
    (localTensorLiftRaw.{c, v, u} φ M N V g)
  have hv := congrArg (fun k ↦ k.app W
    (show (changeOfRingsPresheafOfUniverses φ M).obj (op W.unop.left) from
      s ⊗ₜ[R.obj.obj (op W.unop.left), (φ.hom.app (op W.unop.left)).hom] x)) he
  erw [localTensorAdjunctionEquiv_apply.{c, v, u}] at hv
  change (localTensorLift.{c, v, u} φ M N V g).app W
      (scalarExtensionSection φ M (op W.unop.left) s x) =
    (localTensorLiftRaw.{c, v, u} φ M N V g).app W
      (s ⊗ₜ[R.obj.obj (op W.unop.left), (φ.hom.app (op W.unop.left)).hom] x) at hv
  refine hv.trans ?_
  change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (φ.hom.app (op W.unop.left)).hom (g.app W)
      (s ⊗ₜ[R.obj.obj (op W.unop.left), (φ.hom.app (op W.unop.left)).hom] x) = _
  exact pointFromExtend_tmul (M.val.obj (op W.unop.left))
    (N.val.obj (op W.unop.left)) (φ.hom.app (op W.unop.left)) (g.app W) s x

attribute [local irreducible] localTensorLift

private def sliceRingMap {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (V : Cᵒᵖ) :=
  Functor.whiskerLeft (Over.forget V.unop).op
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom

private def localHomRestrict {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (g : (homObj (R := S) (changeOfRingsOfUniverses φ M) N).val.obj V) :
    (homObj (R := R) M ((moduleRestriction.{c, v, u} φ).obj N)).val.obj V :=
  (PresheafOfModules.restrictOver R.obj V.unop).map
      (scalarSheafHomEquiv.{c, v, u} φ M (changeOfRingsOfUniverses φ M) (𝟙 _)).val ≫
    (PresheafOfModules.restrictScalars (sliceRingMap.{c, v, u} φ V)).map g

private theorem localHomRestrict_apply
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (g : (homObj (R := S) (changeOfRingsOfUniverses φ M) N).val.obj V)
    (W : (Over V.unop)ᵒᵖ) (x : M.val.obj (op W.unop.left)) :
    (localHomRestrict.{c, v, u} φ M N V g).app W x =
      g.app W (scalarExtensionSection φ M (op W.unop.left) 1 x) := by
  change g.app W
      ((scalarSheafHomEquiv.{c, v, u} φ M (changeOfRingsOfUniverses φ M) (𝟙 _)).val.app
        (op W.unop.left) x) = _
  rw [scalarSheafHomEquiv_apply.{c, v, u}]
  rfl

private theorem localTensor_hom_ext
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (f g : (homObj (R := S) (changeOfRingsOfUniverses φ M) N).val.obj V)
    (h : ∀ (W : (Over V.unop)ᵒᵖ) (x : M.val.obj (op W.unop.left)),
      f.app W (scalarExtensionSection φ M (op W.unop.left) 1 x) =
        g.app W (scalarExtensionSection φ M (op W.unop.left) 1 x)) : f = g := by
  apply (localTensorAdjunctionEquiv.{c, v, u} φ M N V).injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.ExtendScalars.hom_ext (f := (φ.hom.app (op W.unop.left)).hom)
  intro x
  erw [localTensorAdjunctionEquiv_apply.{c, v, u},
    localTensorAdjunctionEquiv_apply.{c, v, u}]
  exact h W x

private theorem localHomRestrict_lift
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (g : (homObj (R := R) M ((moduleRestriction.{c, v, u} φ).obj N)).val.obj V) :
    localHomRestrict.{c, v, u} φ M N V (localTensorLift.{c, v, u} φ M N V g) = g := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  rw [localHomRestrict_apply.{c, v, u}, localTensorLift_apply.{c, v, u}, one_smul]

private theorem localTensorLift_restrict
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (g : (homObj (R := S) (changeOfRingsOfUniverses φ M) N).val.obj V) :
    localTensorLift.{c, v, u} φ M N V (localHomRestrict.{c, v, u} φ M N V g) = g := by
  apply localTensor_hom_ext.{c, v, u} φ M N V
  intro W x
  rw [localTensorLift_apply.{c, v, u}, one_smul, localHomRestrict_apply.{c, v, u}]

private def localHomEquiv {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ) :
    (homObj (R := S) (changeOfRingsOfUniverses φ M) N).val.obj V ≃
      (homObj (R := R) M ((moduleRestriction.{c, v, u} φ).obj N)).val.obj V where
  toFun := localHomRestrict.{c, v, u} φ M N V
  invFun := localTensorLift.{c, v, u} φ M N V
  left_inv := localTensorLift_restrict.{c, v, u} φ M N V
  right_inv := localHomRestrict_lift.{c, v, u} φ M N V

private def localHomLinearEquiv {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ) :
    ((moduleRestriction.{c, v, u} φ).obj (homObj (R := S) (changeOfRingsOfUniverses φ M)
      N)).val.obj V ≃ₗ[
      R.obj.obj V] (homObj (R := R) M ((moduleRestriction.{c, v, u} φ).obj N)).val.obj V where
  toEquiv := localHomEquiv.{c, v, u} φ M N V
  map_add' g g' := by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_smul' r g := by
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext x
    change S.obj.map W.unop.hom.op (φ.hom.app V r) •
        g.app W ((scalarSheafHomEquiv.{c, v, u} φ M
          (changeOfRingsOfUniverses φ M) (𝟙 _)).val.app (op W.unop.left) x) =
      φ.hom.app (op W.unop.left) (R.obj.map W.unop.hom.op r) •
        g.app W ((scalarSheafHomEquiv.{c, v, u} φ M
          (changeOfRingsOfUniverses φ M) (𝟙 _)).val.app (op W.unop.left) x)
    erw [scalarSheafHomEquiv_apply.{c, v, u}]
    have h := congrArg (fun k ↦ k r) (φ.hom.naturality W.unop.hom.op)
    exact congrArg (fun z ↦ z •
      g.app W (scalarExtensionSection φ M (op W.unop.left) 1 x)) h.symm

private def moduleTheta {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) :
    (moduleRestriction.{c, v, u} φ).obj (homObj (R := S) (changeOfRingsOfUniverses φ M) N) ≅
      homObj (R := R) M ((moduleRestriction.{c, v, u} φ).obj N) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V ↦ (localHomLinearEquiv.{c, v, u} φ M N V).toModuleIso)
      (by
        intro V V' i
        apply ModuleCat.hom_ext
        ext g
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        ext x
        rfl))

private theorem moduleTheta_apply
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : Mod.{c, v, u} R) (N : Mod.{c, v, u} S) (V : Cᵒᵖ)
    (g : (homObj (R := S) (changeOfRingsOfUniverses φ M) N).val.obj V)
    (W : (Over V.unop)ᵒᵖ) (x : M.val.obj (op W.unop.left)) :
    ((moduleTheta.{c, v, u} φ M N).hom.val.app V g).app W x =
      g.app W (scalarExtensionSection φ M (op W.unop.left) 1 x) := by
  exact localHomRestrict_apply.{c, v, u} φ M N V g W x

attribute [local irreducible] moduleTheta

private def gradedTheta {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S) (n : ℤ) :
    (moduleRestriction.{c, v, u} φ).obj
        ((homComplex (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N).X n) ≅
      (homComplex (R := R) P ((restriction.{c, v, u} φ).obj N)).X n := by
  have := (ordinaryAdjunction.{c, v, u} φ).rightAdjoint_preservesLimits
  exact (isLimitOfPreserves (moduleRestriction.{c, v, u} φ)
    (homComplexIsLimit (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N
      n)).conePointsIsoOfNatIso
      (homComplexIsLimit (R := R) P ((restriction.{c, v, u} φ).obj N) n)
      (Discrete.natIso fun i ↦ moduleTheta.{c, v, u} φ (P.X i.as) (N.X (i.as + n)))

private theorem gradedTheta_π {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (n i k : ℤ) (h : i + n = k) :
    (gradedTheta.{c, v, u} φ P N n).hom ≫ homComplexπ (R := R) P ((restriction.{c, v, u} φ).obj N)
      n i k h =
      (moduleRestriction.{c, v, u} φ).map
          (homComplexπ (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N n i k h) ≫
        (moduleTheta.{c, v, u} φ (P.X i) (N.X k)).hom := by
  subst k
  have := (ordinaryAdjunction.{c, v, u} φ).rightAdjoint_preservesLimits
  exact IsLimit.conePointsIsoOfNatIso_hom_comp
    (isLimitOfPreserves (moduleRestriction.{c, v, u} φ)
      (homComplexIsLimit (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N n))
    (homComplexIsLimit (R := R) P ((restriction.{c, v, u} φ).obj N) n)
    (Discrete.natIso fun j ↦ moduleTheta.{c, v, u} φ (P.X j.as) (N.X (j.as + n)))
    (⟨i⟩ : Discrete ℤ)

private theorem gradedTheta_evaluate
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (g : ((homComplex (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N).X n).val.obj V)
    (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} (R := R) P ((restriction.{c, v, u} φ).obj N) n i k h V
        ((gradedTheta.{c, v, u} φ P N n).hom.val.app V g) x =
      evaluate.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N n i k h V g
        (scalarExtensionSection φ (P.X i) V 1 x) := by
  change (((((gradedTheta.{c, v, u} φ P N n).hom ≫
    homComplexπ (R := R) P ((restriction.{c, v, u} φ).obj N) n i k h).val.app V) g).app
      (op (Over.mk (𝟙 V.unop)))) x = _
  rw [gradedTheta_π.{c, v, u}]
  exact moduleTheta_apply.{c, v, u} φ (P.X i) (N.X k) V
    ((homComplexπ (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N n i k h).val.app V g)
    (op (Over.mk (𝟙 V.unop))) x

attribute [local irreducible] gradedTheta

private theorem hom_section_sub_units {R : Sheaf J CommRingCat.{max c v u}}
    (A B H : Mod.{c, v, u} R) (f g : H ⟶ homObj (R := R) A B) (e : ℤˣ)
    (V : Cᵒᵖ) (s : H.val.obj V) (x : A.val.obj V) :
    ((((f - e • g).val.app V).hom s).app (op (Over.mk (𝟙 V.unop)))).hom x =
      (((f.val.app V).hom s).app (op (Over.mk (𝟙 V.unop)))).hom x -
        e • (((g.val.app V).hom s).app (op (Over.mk (𝟙 V.unop)))).hom x := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let F := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj V
  have he : ((f - e • g).val.app V).hom s =
      (f.val.app V).hom s - e • (g.val.app V).hom s := by
    change (F.map (f - e • g)).hom s = _
    rw [Functor.map_sub]
    simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
      ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
    rfl
  rw [he]
  change (((((f.val.app V).hom s - (e : ℤ) • (g.val.app V).hom s) :
    (PresheafOfModules.restrictOver R.obj V.unop).obj A.val ⟶
      (PresheafOfModules.restrictOver R.obj V.unop).obj B.val).app
        (op (Over.mk (𝟙 V.unop)))).hom x) = _
  erw [PresheafOfModules.sub_app, PresheafOfModules.zsmul_app,
    ModuleCat.hom_sub, ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
  rfl

private theorem evaluate_d {R : Sheaf J CommRingCat.{max c v u}}
    (P N : Complex.{c, v, u} R) (n m i k k' i' : ℤ)
    (hnm : n + 1 = m) (hik : i + m = k) (hik' : i + n = k') (hi'k : i' + n = k)
    (V : Cᵒᵖ) (g : ((homComplex (R := R) P N).X n).val.obj V)
    (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} (R := R) P N m i k hik V (((homComplex (R := R) P N).d n m).val.app V g) x =
      (N.d k' k).val.app V (evaluate.{c, v, u} (R := R) P N n i k' hik' V g x) -
        n.negOnePow • evaluate.{c, v, u} (R := R) P N n i' k hi'k V g ((P.d i i').val.app V x) := by
  have he := congrArg
    (fun f : (homComplex (R := R) P N).X n ⟶ homObj (R := R) (P.X i) (N.X k) ↦
      ((f.val.app V g).app (op (Over.mk (𝟙 V.unop)))).hom x)
    (homComplex_d_π P N n m i k k' i' hnm hik hik' hi'k)
  rw [hom_section_sub_units.{c, v, u}] at he
  exact he

private theorem gradedTheta_comm {R S : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (n m : ℤ) (hnm : n + 1 = m) :
    (gradedTheta.{c, v, u} φ P N n).hom ≫
        (homComplex (R := R) P ((restriction.{c, v, u} φ).obj N)).d n m =
      (moduleRestriction.{c, v, u} φ).map
          ((homComplex (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N).d n m) ≫
        (gradedTheta.{c, v, u} φ P N m).hom := by
  apply evaluate_hom_ext.{c, v, u}
  intro i k hik V g x
  change evaluate.{c, v, u} (R := R) P ((restriction.{c, v, u} φ).obj N) m i k hik V
      (((homComplex (R := R) P ((restriction.{c, v, u} φ).obj N)).d n m).val.app V
        ((gradedTheta.{c, v, u} φ P N n).hom.val.app V g)) x =
    evaluate.{c, v, u} (R := R) P ((restriction.{c, v, u} φ).obj N) m i k hik V
      ((gradedTheta.{c, v, u} φ P N m).hom.val.app V
        (((homComplex (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N).d n m).val.app
          V g)) x
  rw [gradedTheta_evaluate.{c, v, u}]
  rw [evaluate_d.{c, v, u} P ((restriction.{c, v, u} φ).obj N) n m i k (i + n) (i + 1)
    hnm hik rfl (by omega)]
  rw [evaluate_d.{c, v, u} ((canonicalExtension.{c, v, u} φ).complex.obj P) N n m i k (i + n) (i +
    1)
    hnm hik rfl (by omega)]
  rw [gradedTheta_evaluate.{c, v, u}, gradedTheta_evaluate.{c, v, u}]
  have hd := scalarExtension_map_tmul φ (P.d i (i + 1)) V 1 x
  change (((canonicalExtension.{c, v, u} φ).complex.obj P).d i (i + 1)).val.app V
      (scalarExtensionSection φ (P.X i) V 1 x) =
    scalarExtensionSection φ (P.X (i + 1)) V 1 ((P.d i (i + 1)).val.app V x) at hd
  rw [hd]
  rfl

private def chainTheta {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S) :
    (restriction.{c, v, u} φ).obj
        (homComplex (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N) ≅
      homComplex (R := R) P ((restriction.{c, v, u} φ).obj N) :=
  HomologicalComplex.Hom.isoOfComponents (gradedTheta.{c, v, u} φ P N)
    (fun n m h ↦ gradedTheta_comm.{c, v, u} φ P N n m h)

private def presheafRestrictionId (A : Cᵒᵖ ⥤ RingCat.{max c v u}) :
    PresheafOfModules.restrictScalars (𝟙 A) ≅ 𝟭 (PresheafOfModules.{max c v u} A) :=
  Iso.refl _

private theorem presheafRestrictionId_apply (A : Cᵒᵖ ⥤ RingCat.{max c v u})
    (M : PresheafOfModules.{max c v u} A) (V : Cᵒᵖ)
    (x : ((PresheafOfModules.restrictScalars (𝟙 A)).obj M).obj V) :
    ((presheafRestrictionId.{c, v, u} A).hom.app M).app V x = (show M.obj V from x) :=
  rfl

attribute [local irreducible] presheafRestrictionId

private def plainSheafUnit (A : Sheaf J RingCat.{max c v u})
    (M : PresheafOfModules.{max c v u} A.obj) :
    M ⟶ ((PresheafOfModules.sheafification (R := A) (𝟙 A.obj)).obj M).val :=
  (PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 A.obj)).unit.app M ≫
    (presheafRestrictionId.{c, v, u} A.obj).hom.app
      ((PresheafOfModules.sheafification (R := A) (𝟙 A.obj)).obj M).val

private theorem plainSheafUnit_apply (A : Sheaf J RingCat.{max c v u})
    (M : PresheafOfModules.{max c v u} A.obj) (V : Cᵒᵖ) (x : M.obj V) :
    (plainSheafUnit.{c, v, u} A M).app V x =
      ((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 A.obj)).unit.app M).app V x := by
  exact presheafRestrictionId_apply.{c, v, u} A.obj
    ((PresheafOfModules.sheafification (R := A) (𝟙 A.obj)).obj M).val V
      (((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 A.obj)).unit.app M).app V x)

private theorem forget_plainSheafUnit (A : Sheaf J RingCat.{max c v u})
    (M : PresheafOfModules.{max c v u} A.obj) :
    (PresheafOfModules.toPresheaf A.obj).map (plainSheafUnit.{c, v, u} A M) =
      CategoryTheory.toSheafify J M.presheaf := by
  ext V x
  change (plainSheafUnit.{c, v, u} A M).app V x = _
  rw [plainSheafUnit_apply.{c, v, u}]
  exact congrArg (fun f ↦ f.app V x)
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app (𝟙 A.obj) M)

private def restrictedSheafificationHom
    {A B : Sheaf J RingCat.{max c v u}} (φ : A ⟶ B)
    (M : PresheafOfModules.{max c v u} B.obj) :
    (PresheafOfModules.sheafification (R := A) (𝟙 A.obj)).obj
        ((PresheafOfModules.restrictScalars φ.hom).obj M) ⟶
      (restrictScalars φ).obj ((PresheafOfModules.sheafification (R := B) (𝟙 B.obj)).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv (R := A) (𝟙 A.obj)).symm
    ((PresheafOfModules.restrictScalars (𝟙 A.obj)).map
      ((PresheafOfModules.restrictScalars φ.hom).map (plainSheafUnit.{c, v, u} B M)))

private theorem restrictedSheafificationHom_isIso
    {A B : Sheaf J RingCat.{max c v u}} (φ : A ⟶ B)
    (M : PresheafOfModules.{max c v u} B.obj) :
    IsIso (restrictedSheafificationHom.{c, v, u} φ M) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf A)]
  let g := (PresheafOfModules.restrictScalars (𝟙 A.obj)).map
    ((PresheafOfModules.restrictScalars φ.hom).map (plainSheafUnit.{c, v, u} B M))
  have hu : (PresheafOfModules.toPresheaf A.obj).map g =
      CategoryTheory.toSheafify J M.presheaf := by
    ext V x
    exact congrArg (fun f ↦ f.app V x) (forget_plainSheafUnit.{c, v, u} B M)
  have hw : J.W ((PresheafOfModules.toPresheaf A.obj).map g) :=
    hu.symm ▸ J.W_toSheafify M.presheaf
  have hi : IsIso ((presheafToSheaf J AddCommGrpCat.{max c v u}).map
      ((PresheafOfModules.toPresheaf A.obj).map g)) := (J.W_iff _).mp hw
  let F := (restrictScalars φ).obj
    ((PresheafOfModules.sheafification (R := B) (𝟙 B.obj)).obj M)
  have hmap := PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm
    (P := (PresheafOfModules.restrictScalars φ.hom).obj M) (F := F) (𝟙 A.obj) g
  have hl : IsIso (((CategoryTheory.sheafificationAdjunction J
      AddCommGrpCat.{max c v u}).homEquiv _ ((toSheaf A).obj F)).symm
        ((PresheafOfModules.toPresheaf A.obj).map g)) := by
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact hmap.symm ▸ hl

private def restrictedSheafificationIso
    {A B : Sheaf J RingCat.{max c v u}} (φ : A ⟶ B)
    (M : PresheafOfModules.{max c v u} B.obj) :
    (PresheafOfModules.sheafification (R := A) (𝟙 A.obj)).obj
        ((PresheafOfModules.restrictScalars φ.hom).obj M) ≅
      (restrictScalars φ).obj ((PresheafOfModules.sheafification (R := B) (𝟙 B.obj)).obj M) := by
  have := restrictedSheafificationHom_isIso.{c, v, u} φ M
  exact asIso (restrictedSheafificationHom.{c, v, u} φ M)

private theorem restrictedSheafificationIso_pure
    {A B : Sheaf J RingCat.{max c v u}} (φ : A ⟶ B)
    (M : PresheafOfModules.{max c v u} B.obj) (V : Cᵒᵖ) (x : M.obj V) :
    (restrictedSheafificationIso.{c, v, u} φ M).hom.val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 A.obj)).unit.app
          ((PresheafOfModules.restrictScalars φ.hom).obj M)).app V x) =
      ((PresheafOfModules.sheafificationAdjunction (R := B) (𝟙 B.obj)).unit.app M).app V x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars φ.hom).obj M)
    (F := (restrictScalars φ).obj
      ((PresheafOfModules.sheafification (R := B) (𝟙 B.obj)).obj M)) (𝟙 A.obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars (𝟙 A.obj)).map
      ((PresheafOfModules.restrictScalars φ.hom).map (plainSheafUnit.{c, v, u} B M)))
  have hx := congrArg (fun f ↦ f.app V x) h
  change (restrictedSheafificationHom.{c, v, u} φ M).val.app V
      (((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 A.obj)).unit.app
        ((PresheafOfModules.restrictScalars φ.hom).obj M)).app V x) =
    (plainSheafUnit.{c, v, u} B M).app V x at hx
  exact hx.trans (plainSheafUnit_apply.{c, v, u} B M V x)

private def restrictedTensorPresheafIso
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (scalarModule.{c, v, u} φ).val ⊗ M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
          (changeOfRingsPresheafOfUniverses φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let ρ := (φ.hom.app V).hom
    let T := TensorProduct (R.obj.obj V)
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) (S.obj.obj V)))
      (M.val.obj V)
    exact (LinearEquiv.refl (R.obj.obj V) T).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((scalarModule.{c, v, u} φ).val ⊗ M.val).map f z =
      (changeOfRingsPresheafOfUniverses φ M).map f z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s x => exact (changeOfRingsMap_tmulOfUniverses φ M f s x).symm

private theorem abstract_tensor_natural
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) [F.Monoidal] {M₀ N₀ N₁ : A} {M N N' : B}
    (eM : F.obj M₀ ≅ M) (eN : F.obj N₀ ≅ N) (eN' : F.obj N₁ ≅ N')
    (f : N ⟶ N') (g : N₀ ⟶ N₁) (hg : F.map g ≫ eN'.hom = eN.hom ≫ f) :
    M ◁ f ≫ ((eM ⊗ᵢ eN').symm ≪≫ Functor.Monoidal.μIso F M₀ N₁).hom =
      ((eM ⊗ᵢ eN).symm ≪≫ Functor.Monoidal.μIso F M₀ N₀).hom ≫ F.map (M₀ ◁ g) := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Functor.Monoidal.μIso_hom, Category.assoc, ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · apply (cancel_mono eN'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hg]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

attribute [local irreducible] tensorObjIsoSheafification

private def concreteCounitIso (R : Sheaf J CommRingCat.{max c v u})
    (M : Mod.{c, v, u} R) :
    (PresheafOfModules.sheafification.{max c v u}
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction.{max c v u}
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).counit).app M

private theorem concreteCounit_natural (R : Sheaf J CommRingCat.{max c v u})
    {N N' : Mod.{c, v, u} R} (f : N ⟶ N') :
    (PresheafOfModules.sheafification.{max c v u}
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).map f.val ≫
        (concreteCounitIso R N').hom = (concreteCounitIso R N).hom ≫ f := by
  exact (PresheafOfModules.sheafificationAdjunction.{max c v u}
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).counit.naturality f

attribute [local irreducible] concreteCounitIso

private theorem tensorCounit_eq {R : Sheaf J CommRingCat.{max c v u}}
    (M N : Mod.{c, v, u} R) :
    tensorObjIsoSheafification (R := R) M N =
      ((concreteCounitIso R M ⊗ᵢ concreteCounitIso R N).symm ≪≫
        Functor.Monoidal.μIso
          (PresheafOfModules.sheafification.{max c v u}
            (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _))
          M.val N.val) := by
  unfold tensorObjIsoSheafification concreteCounitIso
  rfl

private theorem tensorIso_natural {R : Sheaf J CommRingCat.{max c v u}}
    (M : Mod.{c, v, u} R) {N N' : Mod.{c, v, u} R} (f : N ⟶ N') :
    M ◁ f ≫ (tensorObjIsoSheafification (R := R) M N').hom =
      (tensorObjIsoSheafification (R := R) M N).hom ≫
        (PresheafOfModules.sheafification.{max c v u}
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).map
            (M.val ◁ f.val) := by
  have hn := abstract_tensor_natural
    (PresheafOfModules.sheafification.{max c v u}
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _))
    (concreteCounitIso.{c, v, u} R M) (concreteCounitIso.{c, v, u} R N)
    (concreteCounitIso.{c, v, u} R N') f f.val (concreteCounit_natural.{c, v, u} R f)
  rw [tensorCounit_eq M N', tensorCounit_eq M N]
  exact hn

private def tensorUnitMap {R : Sheaf J CommRingCat.{max c v u}} (M N : Mod.{c, v, u} R) :
    M.val ⊗ N.val ⟶ (M ⊗ N).val :=
  (PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app _ ≫
    (tensorObjIsoSheafification (R := R) M N).inv.val

set_option backward.isDefEq.respectTransparency true in
private theorem tensorUnitMap_natural {R : Sheaf J CommRingCat.{max c v u}}
    (M : Mod.{c, v, u} R) {N N' : Mod.{c, v, u} R} (f : N ⟶ N') :
    tensorUnitMap.{c, v, u} (R := R) M N ≫ (M ◁ f).val =
      (M.val ◁ f.val) ≫ tensorUnitMap.{c, v, u} (R := R) M N' := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have h : (tensorObjIsoSheafification (R := R) M N).inv ≫ M ◁ f =
      (PresheafOfModules.sheafification
        (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).map (M.val ◁ f.val) ≫
        (tensorObjIsoSheafification (R := R) M N').inv := by
    erw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIso_natural.{c, v, u} (R := R),
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold tensorUnitMap
  erw [Category.assoc, ← comp_val, h, comp_val, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ (tensorObjIsoSheafification (R := R) M N').inv.val)
    (adj.unit.naturality (M.val ◁ f.val)).symm

private theorem tensorUnitMap_apply_map {R : Sheaf J CommRingCat.{max c v u}}
    (M : Mod.{c, v, u} R) {N N' : Mod.{c, v, u} R} (f : N ⟶ N') (V : Cᵒᵖ)
    (s : M.val.obj V) (x : N.val.obj V) :
    (M ◁ f).val.app V ((tensorUnitMap.{c, v, u} (R := R) M N).app V (s ⊗ₜ[R.obj.obj V] x)) =
      (tensorUnitMap.{c, v, u} (R := R) M N').app V (s ⊗ₜ[R.obj.obj V] f.val.app V x) := by
  exact congrArg (fun k ↦ k.app V (s ⊗ₜ[R.obj.obj V] x)) (tensorUnitMap_natural.{c, v, u} (R := R)
    M f)

private theorem tensorUnitMap_hom_ext {R : Sheaf J CommRingCat.{max c v u}}
    (M N H : Mod.{c, v, u} R) (f g : M ⊗ N ⟶ H)
    (h : ∀ (V : Cᵒᵖ) (s : M.val.obj V) (x : N.val.obj V),
      f.val.app V ((tensorUnitMap.{c, v, u} (R := R) M N).app V (s ⊗ₜ[R.obj.obj V] x)) =
        g.val.app V ((tensorUnitMap.{c, v, u} (R := R) M N).app V (s ⊗ₜ[R.obj.obj V] x))) : f = g
          := by
  apply (cancel_epi (tensorObjIsoSheafification (R := R) M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).homEquiv _ H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s x
  exact h V s x

private def ordinaryNu {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (scalarModule.{c, v, u} φ) ⊗ M ≅
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (changeOfRingsOfUniverses φ M) :=
  tensorObjIsoSheafification (R := R) _ M ≪≫
    (PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).mapIso
        (restrictedTensorPresheafIso.{c, v, u} φ M) ≪≫
    restrictedSheafificationIso.{c, v, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
      (changeOfRingsPresheafOfUniverses φ M)

private theorem ordinaryNu_pure {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) :
    (ordinaryNu.{c, v, u} φ M).hom.val.app V
        ((tensorObjIsoSheafification (R := R) (scalarModule.{c, v, u} φ) M).inv.val.app V
          (((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app
            ((scalarModule.{c, v, u} φ).val ⊗ M.val)).app V (s ⊗ₜ[R.obj.obj V] x))) =
      scalarExtensionSection φ M V s x := by
  let SR := PresheafOfModules.sheafification
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  let eP := restrictedTensorPresheafIso.{c, v, u} φ M
  let ρ := (sheafCompose J (forget₂ CommRingCat RingCat)).map φ
  let T := changeOfRingsPresheafOfUniverses φ M
  have he : (tensorObjIsoSheafification (R := R) (scalarModule.{c, v, u} φ) M).inv ≫
      (ordinaryNu.{c, v, u} φ M).hom =
      SR.map eP.hom ≫ (restrictedSheafificationIso.{c, v, u} ρ T).hom := by
    dsimp only [SR, eP, ρ, T]
    simp only [ordinaryNu, Iso.trans_hom, Functor.mapIso_hom, Iso.inv_hom_id_assoc]
  have hn := congrArg (fun k ↦ k.app V (s ⊗ₜ[R.obj.obj V] x))
    (adj.unit.naturality eP.hom)
  have hc := congrArg (fun k ↦ k.val.app V
    ((adj.unit.app ((scalarModule.{c, v, u} φ).val ⊗ M.val)).app V (s ⊗ₜ[R.obj.obj V] x))) he
  change (ordinaryNu.{c, v, u} φ M).hom.val.app V
      ((tensorObjIsoSheafification (R := R) (scalarModule.{c, v, u} φ) M).inv.val.app V
        ((adj.unit.app ((scalarModule.{c, v, u} φ).val ⊗ M.val)).app V
          (s ⊗ₜ[R.obj.obj V] x))) =
    (restrictedSheafificationIso.{c, v, u} ρ T).hom.val.app V
    ((SR.map eP.hom).val.app V
      ((adj.unit.app ((scalarModule.{c, v, u} φ).val ⊗ M.val)).app V (s ⊗ₜ[R.obj.obj V] x))) at hc
  erw [hc]
  change (adj.unit.app ((PresheafOfModules.restrictScalars ρ.hom).obj T)).app V
      (eP.hom.app V (s ⊗ₜ[R.obj.obj V] x)) =
    (SR.map eP.hom).val.app V
      ((adj.unit.app ((scalarModule.{c, v, u} φ).val ⊗ M.val)).app V (s ⊗ₜ[R.obj.obj V] x)) at hn
  rw [← hn]
  exact restrictedSheafificationIso_pure.{c, v, u} ρ T V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)

private theorem ordinaryNu_natural
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    {M N : Mod.{c, v, u} R} (f : M ⟶ N) :
    (scalarModule.{c, v, u} φ) ◁ f ≫ (ordinaryNu.{c, v, u} φ N).hom =
      (ordinaryNu.{c, v, u} φ M).hom ≫ (moduleRestriction.{c, v, u} φ).map ((ordinaryExtension.{c,
        v, u} φ).map f) := by
  apply tensorUnitMap_hom_ext.{c, v, u} (R := R)
  intro V s x
  change (ordinaryNu.{c, v, u} φ N).hom.val.app V
      (((scalarModule.{c, v, u} φ) ◁ f).val.app V
        ((tensorUnitMap.{c, v, u} (R := R) (scalarModule.{c, v, u} φ) M).app V (s ⊗ₜ[R.obj.obj V]
          x))) =
    (changeOfRingsHomOfUniverses φ M f).val.app V
      ((ordinaryNu.{c, v, u} φ M).hom.val.app V
        ((tensorUnitMap.{c, v, u} (R := R) (scalarModule.{c, v, u} φ) M).app V (s ⊗ₜ[R.obj.obj V]
          x)))
  rw [tensorUnitMap_apply_map.{c, v, u} (R := R)]
  rw [show (ordinaryNu.{c, v, u} φ N).hom.val.app V
      ((tensorUnitMap.{c, v, u} (R := R) (scalarModule.{c, v, u} φ) N).app V
        (s ⊗ₜ[R.obj.obj V] f.val.app V x)) =
      scalarExtensionSection φ N V s (f.val.app V x) from ordinaryNu_pure.{c, v, u} φ N V s _]
  rw [show (ordinaryNu.{c, v, u} φ M).hom.val.app V
      ((tensorUnitMap.{c, v, u} (R := R) (scalarModule.{c, v, u} φ) M).app V (s ⊗ₜ[R.obj.obj V] x))
        =
      scalarExtensionSection φ M V s x from ordinaryNu_pure.{c, v, u} φ M V s x]
  exact (scalarExtension_map_tmul φ f V s x).symm

private def moduleNu {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    tensorLeft (scalarModule.{c, v, u} φ) ≅
      ordinaryExtension.{c, v, u} φ ⋙ moduleRestriction.{c, v, u} φ :=
  NatIso.ofComponents (ordinaryNu.{c, v, u} φ) (by
    intro M N f
    exact ordinaryNu_natural.{c, v, u} φ f)

private def chainNu {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    tensor.{c, v, u} φ ≅ (canonicalExtension.{c, v, u} φ).complex ⋙ restriction.{c, v, u} φ :=
  (Functor.mapHomologicalComplexCompIso (moduleNu.{c, v, u} φ).symm (.up ℤ)).symm

private theorem chainNu_pure {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (A.X n).val.obj V) :
    (((chainNu.{c, v, u} φ).app A).hom.f n).val.app V (tensorSection.{c, v, u} φ A n V s x) =
      scalarExtensionSection φ (A.X n) V s x := by
  exact ordinaryNu_pure.{c, v, u} φ (A.X n) V s x

private def chainAdjunction {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    (canonicalExtension.{c, v, u} φ).complex ⊣ restriction.{c, v, u} φ :=
  (ordinaryAdjunction.{c, v, u} φ).mapHomologicalComplex (.up ℤ)

private theorem chainAdjunction_unit_pure
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ) (x : (A.X n).val.obj V) :
    (((chainAdjunction.{c, v, u} φ).unit.app A).f n).val.app V x =
      scalarExtensionSection φ (A.X n) V 1 x := by
  unfold chainAdjunction ordinaryAdjunction
  change (scalarSheafHomEquiv.{c, v, u} φ (A.X n)
    (changeOfRingsOfUniverses φ (A.X n)) (𝟙 _)).val.app V x = _
  rw [scalarSheafHomEquiv_apply.{c, v, u}]
  rfl

attribute [local irreducible] chainAdjunction
attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection

private def chainSigma {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : (canonicalExtension.{c, v, u} φ).complex.obj A ⟶ N) :
    (canonicalExtension.{c, v, u} φ).complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N :=
  ((chainAdjunction.{c, v, u} φ).homEquiv _ _).symm
    (homMap.{c, v, u} (R := R) (𝟙 P) ((chainAdjunction.{c, v, u} φ).unit.app A ≫ (restriction.{c,
      v, u} φ).map q) ≫
      (chainTheta.{c, v, u} φ P N).inv)

private theorem chainSigma_transpose
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : (canonicalExtension.{c, v, u} φ).complex.obj A ⟶ N) :
    (chainAdjunction.{c, v, u} φ).unit.app (homComplex (R := R) P A) ≫
        (restriction.{c, v, u} φ).map (chainSigma.{c, v, u} φ P A N q) ≫ (chainTheta.{c, v, u} φ P
          N).hom =
      homMap.{c, v, u} (R := R) (𝟙 P) ((chainAdjunction.{c, v, u} φ).unit.app A ≫ (restriction.{c,
        v, u} φ).map q) := by
  change ((chainAdjunction.{c, v, u} φ).homEquiv _ _
    (chainSigma.{c, v, u} φ P A N q)) ≫ (chainTheta.{c, v, u} φ P N).hom = _
  unfold chainSigma
  rw [Equiv.apply_symm_apply]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

attribute [local irreducible] chainSigma

private def moduleEvaluate {R : Sheaf J CommRingCat.{max c v u}}
    (M N : Mod.{c, v, u} R) (V : Cᵒᵖ) :
    (homObj (R := R) M N).val.obj V →ₗ[R.obj.obj V]
      M.val.obj V →ₗ[R.obj.obj V] N.val.obj V where
  toFun g := (g.app (op (Over.mk (𝟙 V.unop)))).hom
  map_add' _ _ := rfl
  map_smul' r g := by
    ext x
    rw [PresheafOfModules.smul_app, ModuleCat.hom_comp, LinearMap.comp_apply,
      PresheafOfModules.sectionsSMul_app_apply, PresheafOfModules.overSections_coe_apply]
    simp

private theorem evaluate_smul {R : Sheaf J CommRingCat.{max c v u}}
    (P N : Complex.{c, v, u} R) (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (s t : R.obj.obj V) (g : ((homComplex (R := R) P N).X n).val.obj V)
    (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} (R := R) P N n i k h V (s • g) (t • x) =
      (s * t) • evaluate.{c, v, u} (R := R) P N n i k h V g x := by
  let ev := moduleEvaluate.{c, v, u} (P.X i) (N.X k) V
  change ev (((homComplexπ (R := R) P N n i k h).val.app V).hom (s • g)) (t • x) =
    (s * t) • ev (((homComplexπ (R := R) P N n i k h).val.app V).hom g) x
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [mul_comm t s]

private theorem chainSigma_unit_evaluate
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : (canonicalExtension.{c, v, u} φ).complex.obj A ⟶ N)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N n i k h V
        (((chainSigma.{c, v, u} φ P A N q).f n).val.app V
          (scalarExtensionSection φ ((homComplex (R := R) P A).X n) V 1 f))
        (scalarExtensionSection φ (P.X i) V 1 x) =
      (q.f k).val.app V
        (scalarExtensionSection φ (A.X k) V 1 (evaluate.{c, v, u} (R := R) P A n i k h V f x)) := by
  have he := congrArg (fun t ↦ evaluate.{c, v, u} (R := R) P ((restriction.{c, v, u} φ).obj N) n i
    k h V
    ((t.f n).val.app V f) x) (chainSigma_transpose.{c, v, u} φ P A N q)
  change evaluate.{c, v, u} (R := R) P ((restriction.{c, v, u} φ).obj N) n i k h V
      ((gradedTheta.{c, v, u} φ P N n).hom.val.app V
        (((chainSigma.{c, v, u} φ P A N q).f n).val.app V
          ((((chainAdjunction.{c, v, u} φ).unit.app (homComplex (R := R) P A)).f n).val.app V f)))
      x = _ at he
  rw [gradedTheta_evaluate.{c, v, u}, chainAdjunction_unit_pure.{c, v, u}] at he
  erw [evaluate_homMap.{c, v, u} (𝟙 P)
    ((chainAdjunction.{c, v, u} φ).unit.app A ≫ (restriction.{c, v, u} φ).map q)
    n i k h V f x] at he
  change _ = (q.f k).val.app V
    ((((chainAdjunction.{c, v, u} φ).unit.app A).f k).val.app V
      (evaluate.{c, v, u} (R := R) P A n i k h V f x)) at he
  rw [chainAdjunction_unit_pure.{c, v, u}] at he
  exact he

private theorem chainSigma_formula
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : (canonicalExtension.{c, v, u} φ).complex.obj A ⟶ N) :
    SigmaFormula.{c, v, u} (canonicalExtension.{c, v, u} φ) P A N q (chainSigma.{c, v, u} φ P A N
      q) := by
  intro n i k h V s t f x
  change evaluate.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N n i k h V
      (((chainSigma.{c, v, u} φ P A N q).f n).val.app V
        (scalarExtensionSection φ ((homComplex (R := R) P A).X n) V s f))
      (scalarExtensionSection φ (P.X i) V t x) = _
  rw [← mul_one s, ← scalarExtensionSection_smul, map_smul]
  rw [← mul_one t, ← scalarExtensionSection_smul, evaluate_smul.{c, v, u}]
  rw [chainSigma_unit_evaluate.{c, v, u}]
  simp only [mul_one]
  rfl

private theorem scalarHom_ext
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (H P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (a b : (canonicalExtension.{c, v, u} φ).complex.obj H ⟶
      homComplex (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N)
    (hab : ∀ (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
      (f : (H.X n).val.obj V) (x : (P.X i).val.obj V),
      evaluate.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N n i k h V
          ((a.f n).val.app V (scalarExtensionSection φ (H.X n) V 1 f))
          (scalarExtensionSection φ (P.X i) V 1 x) =
        evaluate.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N n i k h V
          ((b.f n).val.app V (scalarExtensionSection φ (H.X n) V 1 f))
          (scalarExtensionSection φ (P.X i) V 1 x)) : a = b := by
  apply ((chainAdjunction.{c, v, u} φ).homEquiv H _).injective
  apply (cancel_mono (chainTheta.{c, v, u} φ P N).hom).mp
  apply HomologicalComplex.hom_ext
  intro n
  apply evaluate_hom_ext.{c, v, u}
  intro i k h V f x
  change evaluate.{c, v, u} (R := R) P ((restriction.{c, v, u} φ).obj N) n i k h V
      ((gradedTheta.{c, v, u} φ P N n).hom.val.app V
        ((a.f n).val.app V ((((chainAdjunction.{c, v, u} φ).unit.app H).f n).val.app V f))) x =
    evaluate.{c, v, u} (R := R) P ((restriction.{c, v, u} φ).obj N) n i k h V
      ((gradedTheta.{c, v, u} φ P N n).hom.val.app V
        ((b.f n).val.app V ((((chainAdjunction.{c, v, u} φ).unit.app H).f n).val.app V f))) x
  erw [gradedTheta_evaluate.{c, v, u} φ P N n i k h V
      ((a.f n).val.app V ((((chainAdjunction.{c, v, u} φ).unit.app H).f n).val.app V f)) x,
    gradedTheta_evaluate.{c, v, u} φ P N n i k h V
      ((b.f n).val.app V ((((chainAdjunction.{c, v, u} φ).unit.app H).f n).val.app V f)) x,
    chainAdjunction_unit_pure.{c, v, u} φ H n V f]
  exact hab n i k h V f x

private theorem chainSigma_unique
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : (canonicalExtension.{c, v, u} φ).complex.obj A ⟶ N)
    (s : (canonicalExtension.{c, v, u} φ).complex.obj (homComplex (R := R) P A) ⟶
      homComplex (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N)
    (hs : SigmaFormula.{c, v, u} (canonicalExtension.{c, v, u} φ) P A N q s) : s = chainSigma.{c,
      v, u} φ P A N q := by
  apply scalarHom_ext.{c, v, u} φ (homComplex (R := R) P A) P N
  intro n i k h V f x
  rw [chainSigma_unit_evaluate.{c, v, u}]
  have hh := hs n i k h V 1 1 f x
  change evaluate.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P) N
      n i k h V ((s.f n).val.app V
        (scalarExtensionSection φ ((homComplex (R := R) P A).X n) V 1 f))
      (scalarExtensionSection φ (P.X i) V 1 x) =
    (1 * 1) • (q.f k).val.app V (scalarExtensionSection φ (A.X k) V 1
      (evaluate.{c, v, u} (R := R) P A n i k h V f x)) at hh
  simpa only [one_mul, one_smul] using hh

private theorem chainTheta_natural
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P P' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
    (a : P' ⟶ P) (w : N ⟶ N') :
    (restriction.{c, v, u} φ).map (homMap.{c, v, u} (R := S) ((canonicalExtension.{c, v, u}
      φ).complex.map a) w) ≫
        (chainTheta.{c, v, u} φ P' N').hom =
      (chainTheta.{c, v, u} φ P N).hom ≫ homMap.{c, v, u} (R := R) a ((restriction.{c, v, u} φ).map
        w) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply evaluate_hom_ext.{c, v, u}
  intro i k h V g x
  change evaluate.{c, v, u} (R := R) P' ((restriction.{c, v, u} φ).obj N') n i k h V
      ((gradedTheta.{c, v, u} φ P' N' n).hom.val.app V
        (((homMap.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.map a) w).f
          n).val.app V g)) x =
    evaluate.{c, v, u} (R := R) P' ((restriction.{c, v, u} φ).obj N') n i k h V
      (((homMap.{c, v, u} (R := R) a ((restriction.{c, v, u} φ).map w)).f n).val.app V
        ((gradedTheta.{c, v, u} φ P N n).hom.val.app V g)) x
  rw [gradedTheta_evaluate.{c, v, u}, evaluate_homMap.{c, v, u}, evaluate_homMap.{c, v, u},
    gradedTheta_evaluate.{c, v, u}]
  have ha := scalarExtension_map_tmul φ (a.f i) V 1 x
  change ((((canonicalExtension.{c, v, u} φ).complex.map a).f i).val.app V
      (scalarExtensionSection φ (P'.X i) V 1 x)) = _ at ha
  rw [ha]
  rfl

private theorem homMap_id {R : Sheaf J CommRingCat.{max c v u}}
    (P A : Complex.{c, v, u} R) : homMap.{c, v, u} (R := R) (𝟙 P) (𝟙 A) = 𝟙 (homComplex (R := R) P
      A) := by
  simp only [homMap, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app]
  exact Category.id_comp _

private theorem homMap_comp {R : Sheaf J CommRingCat.{max c v u}}
    {P P' P'' A A' A'' : Complex.{c, v, u} R}
    (a : P' ⟶ P) (a' : P'' ⟶ P') (b : A ⟶ A') (b' : A' ⟶ A'') :
    homMap.{c, v, u} (R := R) a b ≫ homMap.{c, v, u} (R := R) a' b' = homMap.{c, v, u} (R := R) (a'
      ≫ a) (b ≫ b') := by
  simp only [homMap, Category.assoc]
  rw [← Category.assoc ((homComplexFunctor.obj (op P')).map b),
    (homComplexFunctor.map a'.op).naturality, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← Category.assoc, ← NatTrans.comp_app,
    ← CategoryTheory.Functor.map_comp, ← op_comp]

private theorem chainSigma_natural
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P P' A A' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
    (q : (canonicalExtension.{c, v, u} φ).complex.obj A ⟶ N)
    (q' : (canonicalExtension.{c, v, u} φ).complex.obj A' ⟶ N')
    (a : P' ⟶ P) (b : A ⟶ A') (w : N ⟶ N')
    (hq : (canonicalExtension.{c, v, u} φ).complex.map b ≫ q' = q ≫ w) :
    (canonicalExtension.{c, v, u} φ).complex.map (homMap.{c, v, u} (R := R) a b) ≫ chainSigma.{c,
      v, u} φ P' A' N' q' =
      chainSigma.{c, v, u} φ P A N q ≫ homMap.{c, v, u} (R := S) ((canonicalExtension.{c, v, u}
        φ).complex.map a) w := by
  apply scalarHom_ext.{c, v, u} φ (homComplex (R := R) P A) P' N'
  intro n i k h V f x
  change evaluate.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P') N' n i k h V
      (((chainSigma.{c, v, u} φ P' A' N' q').f n).val.app V
        ((((canonicalExtension.{c, v, u} φ).complex.map (homMap.{c, v, u} (R := R) a b)).f
          n).val.app V
          (scalarExtensionSection φ ((homComplex (R := R) P A).X n) V 1 f)))
      (scalarExtensionSection φ (P'.X i) V 1 x) =
    evaluate.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P') N' n i k h V
      (((homMap.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.map a) w).f n).val.app
        V
        (((chainSigma.{c, v, u} φ P A N q).f n).val.app V
          (scalarExtensionSection φ ((homComplex (R := R) P A).X n) V 1 f)))
      (scalarExtensionSection φ (P'.X i) V 1 x)
  have hm := scalarExtension_map_tmul φ ((homMap.{c, v, u} (R := R) a b).f n) V 1 f
  change ((((canonicalExtension.{c, v, u} φ).complex.map (homMap.{c, v, u} (R := R) a b)).f
    n).val.app V
      (scalarExtensionSection φ ((homComplex (R := R) P A).X n) V 1 f)) = _ at hm
  rw [hm, chainSigma_unit_evaluate.{c, v, u}, evaluate_homMap.{c, v, u}, evaluate_homMap.{c, v, u}]
  have ha := scalarExtension_map_tmul φ (a.f i) V 1 x
  change ((((canonicalExtension.{c, v, u} φ).complex.map a).f i).val.app V
      (scalarExtensionSection φ (P'.X i) V 1 x)) = _ at ha
  rw [ha, chainSigma_unit_evaluate.{c, v, u}]
  have he := congrArg (fun t ↦ (t.f k).val.app V
    (scalarExtensionSection φ (A.X k) V 1
      (evaluate.{c, v, u} (R := R) P A n i k h V f ((a.f i).val.app V x)))) hq
  change (q'.f k).val.app V
      ((changeOfRingsHomOfUniverses φ (A.X k) (b.f k)).val.app V
        (scalarExtensionSection φ (A.X k) V 1
          (evaluate.{c, v, u} (R := R) P A n i k h V f ((a.f i).val.app V x)))) = _ at he
  rw [scalarExtension_map_tmul] at he
  exact he

private theorem chainSigma_postcomp
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : (canonicalExtension.{c, v, u} φ).complex.obj A ⟶ N) :
    chainSigma.{c, v, u} φ P A N q =
      chainSigma.{c, v, u} φ P A ((canonicalExtension.{c, v, u} φ).complex.obj A) (𝟙 _) ≫
        homMap.{c, v, u} (R := S) (𝟙 _) q := by
  have h := chainSigma_natural.{c, v, u} φ P P A A ((canonicalExtension.{c, v, u} φ).complex.obj A)
    N
    (𝟙 _) q (𝟙 P) (𝟙 A) q (by simp)
  rw [homMap_id.{c, v, u}] at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

private def chainAlpha {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P A : Complex.{c, v, u} R) :
    (tensor.{c, v, u} φ).obj (homComplex (R := R) P A) ⟶
      homComplex (R := R) P ((tensor.{c, v, u} φ).obj A) :=
  ((chainNu.{c, v, u} φ).app (homComplex (R := R) P A)).hom ≫
    (restriction.{c, v, u} φ).map
      (chainSigma.{c, v, u} φ P A ((canonicalExtension.{c, v, u} φ).complex.obj A) (𝟙 _)) ≫
    (chainTheta.{c, v, u} φ P ((canonicalExtension.{c, v, u} φ).complex.obj A)).hom ≫
    homMap.{c, v, u} (R := R) (𝟙 P) ((chainNu.{c, v, u} φ).app A).inv

private theorem chainNu_inv_pure
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (A.X n).val.obj V) :
    ((((chainNu.{c, v, u} φ).app A).inv.f n).val.app V)
        (scalarExtensionSection φ (A.X n) V s x) = tensorSection.{c, v, u} φ A n V s x := by
  erw [← chainNu_pure.{c, v, u} φ A n V s x]
  have h := congrArg (fun t ↦ (t.f n).val.app V (tensorSection.{c, v, u} φ A n V s x))
    (((chainNu.{c, v, u} φ).app A).hom_inv_id)
  exact h

attribute [local irreducible] chainNu homMap tensorObj homComplex homComplexπ in
set_option backward.isDefEq.respectTransparency true in
private theorem chainAlpha_evaluate
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P A : Complex.{c, v, u} R) (n i k : ℤ) (h : i + n = k)
    (V : Cᵒᵖ) (s : S.obj.obj V)
    (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V) :
    evaluate.{c, v, u} (R := R) P ((tensor.{c, v, u} φ).obj A) n i k h V
        (((chainAlpha.{c, v, u} φ P A).f n).val.app V
          (tensorSection.{c, v, u} φ (homComplex (R := R) P A) n V s f)) x =
      tensorSection.{c, v, u} φ A k V s (evaluate.{c, v, u} (R := R) P A n i k h V f x) := by
  change evaluate.{c, v, u} (R := R) P ((tensor.{c, v, u} φ).obj A) n i k h V
      (((homMap.{c, v, u} (R := R) (𝟙 P) ((chainNu.{c, v, u} φ).app A).inv).f n).val.app V
        ((gradedTheta.{c, v, u} φ P ((canonicalExtension.{c, v, u} φ).complex.obj A) n).hom.val.app
          V
          (((chainSigma.{c, v, u} φ P A ((canonicalExtension.{c, v, u} φ).complex.obj A) (𝟙 _)).f
            n).val.app V
            ((((chainNu.{c, v, u} φ).app (homComplex (R := R) P A)).hom.f n).val.app V
              (tensorSection.{c, v, u} φ (homComplex (R := R) P A) n V s f))))) x = _
  erw [chainNu_pure.{c, v, u}, evaluate_homMap.{c, v, u},
    gradedTheta_evaluate.{c, v, u}]
  simp only [HomologicalComplex.id_f, id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  have hs := chainSigma_formula.{c, v, u} φ P A ((canonicalExtension.{c, v, u} φ).complex.obj A) (𝟙
    _)
    n i k h V s 1 f x
  change evaluate.{c, v, u} (R := S) ((canonicalExtension.{c, v, u} φ).complex.obj P)
      ((canonicalExtension.{c, v, u} φ).complex.obj A) n i k h V
      (((chainSigma.{c, v, u} φ P A ((canonicalExtension.{c, v, u} φ).complex.obj A) (𝟙 _)).f
        n).val.app V
        (scalarExtensionSection φ ((homComplex (R := R) P A).X n) V s f))
      (scalarExtensionSection φ (P.X i) V 1 x) = _ at hs
  erw [hs]
  change ((((chainNu.{c, v, u} φ).app A).inv.f k).val.app V)
      ((s * 1) • scalarExtensionSection φ (A.X k) V 1
        (evaluate.{c, v, u} (R := R) P A n i k h V f x)) = _
  erw [mul_one, scalarExtensionSection_smul, mul_one, chainNu_inv_pure.{c, v, u}]

private theorem chainSquare
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (q : (canonicalExtension.{c, v, u} φ).complex.obj A ⟶ N) :
    ((chainNu.{c, v, u} φ).app (homComplex (R := R) P A)).hom ≫
        (restriction.{c, v, u} φ).map (chainSigma.{c, v, u} φ P A N q) ≫ (chainTheta.{c, v, u} φ P
          N).hom =
      chainAlpha.{c, v, u} φ P A ≫ homMap.{c, v, u} (R := R) (𝟙 P) ((chainNu.{c, v, u} φ).app
        A).hom ≫
        homMap.{c, v, u} (R := R) (𝟙 P) ((restriction.{c, v, u} φ).map q) := by
  have ht := chainTheta_natural.{c, v, u} φ P P ((canonicalExtension.{c, v, u} φ).complex.obj A) N
    (𝟙 P) q
  simp only [CategoryTheory.Functor.map_id] at ht
  rw [chainSigma_postcomp.{c, v, u}, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [ht]
  unfold chainAlpha
  simp only [Category.assoc]
  congr 2
  rw [← Category.assoc (homMap.{c, v, u} (R := R) (𝟙 P) ((chainNu.{c, v, u} φ).app A).inv),
    homMap_comp.{c, v, u}]
  simp only [Category.id_comp, Iso.inv_hom_id, homMap_id.{c, v, u}, Category.id_comp]

attribute [local irreducible] chainAlpha chainNu chainTheta homMap in
attribute [local irreducible] tensor homComplex homComplexπ in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem chainAlpha_natural
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S)
    (P P' A A' : Complex.{c, v, u} R) (a : P' ⟶ P) (b : A ⟶ A') :
    (tensor.{c, v, u} φ).map (homMap.{c, v, u} (R := R) a b) ≫ chainAlpha.{c, v, u} φ P' A' =
      chainAlpha.{c, v, u} φ P A ≫ homMap.{c, v, u} (R := R) a ((tensor.{c, v, u} φ).map b) := by
  let E := (canonicalExtension.{c, v, u} φ).complex
  let U := restriction.{c, v, u} φ
  have hn := (chainNu.{c, v, u} φ).hom.naturality (homMap.{c, v, u} (R := R) a b)
  have hs := chainSigma_natural.{c, v, u} φ P P' A A' (E.obj A) (E.obj A')
    (𝟙 _) (𝟙 _) a b (E.map b) (by simp only [Category.comp_id, Category.id_comp]; rfl)
  have ht := chainTheta_natural.{c, v, u} φ P P' (E.obj A) (E.obj A') a (E.map b)
  have hi := (chainNu.{c, v, u} φ).inv.naturality b
  simp only [CategoryTheory.Functor.comp_map] at hn hi
  dsimp only [E] at hs ht
  unfold chainAlpha
  simp only [Category.assoc, Iso.app_hom, Iso.app_inv]
  rw [reassoc_of% hn, ← CategoryTheory.Functor.map_comp_assoc, hs,
    CategoryTheory.Functor.map_comp, Category.assoc, reassoc_of% ht]
  simp only [homMap_comp.{c, v, u}, Category.id_comp, Category.comp_id]
  rw [hi]

private def canonicalData {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    Data.{c, v, u} φ where
  extension := canonicalExtension.{c, v, u} φ
  nu := chainNu.{c, v, u} φ
  nu_pure := chainNu_pure.{c, v, u} φ
  theta := chainTheta.{c, v, u} φ
  theta_evaluate := gradedTheta_evaluate.{c, v, u} φ
  alpha := chainAlpha.{c, v, u} φ
  alpha_evaluate := chainAlpha_evaluate.{c, v, u} φ
  sigma := chainSigma.{c, v, u} φ
  sigma_formula := chainSigma_formula.{c, v, u} φ
  sigma_unique := chainSigma_unique.{c, v, u} φ
  square := chainSquare.{c, v, u} φ
  theta_natural := chainTheta_natural.{c, v, u} φ
  alpha_natural := chainAlpha_natural.{c, v, u} φ
  sigma_natural := chainSigma_natural.{c, v, u} φ

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false

-- Prove coefficient coherence using only normalized data. Keeping these calculations
-- abstract avoids unfolding the concrete sheafifications when comparing composite maps.
private theorem extension_section_smul
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (A.X n).val.obj V) :
    E.section A n V s x = s • E.section A n V 1 x := by
  unfold Extension.section
  erw [← mul_one s, ← scalarExtensionSection_smul, map_smul, mul_one]

private theorem extension_hom_ext
    {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) (H : Complex.{c, v, u} R)
    (N : Complex.{c, v, u} S) (f g : E.complex.obj H ⟶ N)
    (hfg : ∀ (n : ℤ) (V : Cᵒᵖ) (x : (H.X n).val.obj V),
      (f.f n).val.app V (E.section H n V 1 x) =
        (g.f n).val.app V (E.section H n V 1 x)) : f = g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply (cancel_epi (eqToHom (E.obj_eq (H.X n)).symm)).mp
  apply scalarExtension_hom_ext φ (H.X n)
  intro V s x
  change (f.f n).val.app V (E.section H n V s x) =
    (g.f n).val.app V (E.section H n V s x)
  rw [extension_section_smul E H n V s x, map_smul, map_smul, hfg]

end SheafOfModules.StrictScalarHom
