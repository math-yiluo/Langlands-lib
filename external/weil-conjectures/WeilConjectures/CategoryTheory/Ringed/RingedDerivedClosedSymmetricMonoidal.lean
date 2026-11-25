/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
public import Mathlib.Algebra.Category.Grp.FilteredColimits
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
public import Mathlib.CategoryTheory.Sites.Equivalence
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Monoidal.Category

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
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
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Closed symmetric monoidal derived categories of ringed sites

Source: Stacks Project, Cohomology on Sites, Tags 0FPT and 08J9
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal).

The representative equations below specify the actual associator, unitors and Koszul
symmetry, in addition to the closed adjunction for the recorded derived internal Hom.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- A transparent spelling of the recorded ringed-site module category.
Source: Stacks 0FPT (blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
abbrev RingedTensorModules :=
  ringedSiteModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)

/-- The coefficient ring placed in degree zero, using the actual single-complex functor.
Source: Stacks 0FPT (blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
def ringedTensorUnitComplex : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).obj
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))

/-- The actual degree-zero section of the coefficient-ring complex.
Source: Stacks 0FPT (blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
def ringedTensorUnitSection (U : Cᵒᵖ) (a : R.obj.obj U) :
    ((ringedTensorUnitComplex.{c, v, u} J R).X 0).val.obj U :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))).inv.val.app U) a

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- Total-tensor comparison data for all pairs with at least one K-flat factor.
Source: Stacks 06YT and 0FPT
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
def RingedDerivedTensorComparison
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R)) :=
  ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ),
    (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∨
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) →
    (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) ≅
      S.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))

/-- Agreement with the already recorded simultaneous K-flat comparison.
Source: Stacks 0FPT and the signed total tensor of 06YN
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
def RingedDerivedTensorBothModel
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (tensorIso : RingedDerivedTensorComparison.{c, v, u, w} J R S) : Prop :=
  ∀ P Q hP hQ,
    tensorIso P Q (Or.inl hP) = T.iso J R S P Q hP hQ

/-- Naturality on all allowed representatives, including quasi-isomorphisms.
Source: Stacks 0FPT and the signed total tensor of 06YN
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
def RingedDerivedTensorNaturality
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (tensorIso : RingedDerivedTensorComparison.{c, v, u, w} J R S) : Prop :=
  ∀ P Q P' Q' h h' (f : P ⟶ P') (g : Q ⟶ Q'),
    DerivedCategory.Q.map ((coefficientTotalTensor.{u, c, v} J R).map (f, g)) ≫
      (tensorIso P' Q' h').hom =
    (tensorIso P Q h).hom ≫ S.tensor.map (DerivedCategory.Q.map f, DerivedCategory.Q.map g)

/-- The symmetry is induced by the signed swap on every K-flat tensor model.
Source: Stacks 0FPT and the signed total tensor of 06YN
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
def RingedDerivedTensorSymmetryModel
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal) : Prop :=
  ∀ P Q hP hQ,
    ∃ s : (coefficientTotalTensor.{u, c, v} J R).obj (P, Q) ≅
        (coefficientTotalTensor.{u, c, v} J R).obj (Q, P),
      (∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (s.hom.f n).val.app U
          (coefficientTensorGenerator.{u, c, v} J R P Q p q n h U x y) =
        (p * q).negOnePow • coefficientTensorGenerator.{u, c, v} J R Q P q p n h' U y x) ∧
      (T.iso J R S P Q hP hQ).hom ≫
        (β.toBraidedCategory.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map s.hom ≫ (T.iso J R S Q P hQ hP).hom

/-- Reassociation is induced by reassociation of pure-tensor summands, without a sign.
Source: Stacks 0FPT and the signed total tensor of 06YN
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
def RingedDerivedTensorAssociatorModel
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (tensorIso : RingedDerivedTensorComparison.{c, v, u, w} J R S) : Prop :=
  ∀ P Q N hP hQ hN,
    ∃ a : (coefficientTotalTensor.{u, c, v} J R).obj
        ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q), N) ≅
      (coefficientTotalTensor.{u, c, v} J R).obj
        (P, (coefficientTotalTensor.{u, c, v} J R).obj (Q, N)),
      (∀ (p q r pq qr n : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
        (hn : pq + r = n) (hn' : p + qr = n) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X r).val.obj U),
        (a.hom.f n).val.app U
          (coefficientTensorGenerator.{u, c, v} J R
            ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) N pq r n hn U
            (coefficientTensorGenerator.{u, c, v} J R P Q p q pq hpq U x y) z) =
        coefficientTensorGenerator.{u, c, v} J R P
          ((coefficientTotalTensor.{u, c, v} J R).obj (Q, N)) p qr n hn' U x
          (coefficientTensorGenerator.{u, c, v} J R Q N q r qr hqr U y z)) ∧
      (tensorIso ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) N (Or.inr hN)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)),
            DerivedCategory.Q.obj N))
          (Y := (S.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q),
            DerivedCategory.Q.obj N))
          ((T.iso J R S P Q hP hQ).hom, 𝟙 _) ≫
        (S.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom =
      DerivedCategory.Q.map a.hom ≫
        (tensorIso P ((coefficientTotalTensor.{u, c, v} J R).obj (Q, N)) (Or.inl hP)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj P,
            DerivedCategory.Q.obj ((coefficientTotalTensor.{u, c, v} J R).obj (Q, N))))
          (Y := (DerivedCategory.Q.obj P,
            S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)))
          (𝟙 _, (T.iso J R S Q N hQ hN).hom)

/-- The left unitor is multiplication by the degree-zero coefficient.
Source: Stacks 0FPT and the signed total tensor of 06YN
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
def RingedDerivedTensorLeftUnitorModel
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (tensorIso : RingedDerivedTensorComparison.{c, v, u, w} J R S)
    (unitIso : S.monoidal.tensorUnit ≅
      DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)) : Prop :=
  ∀ P hP,
    ∃ l : (coefficientTotalTensor.{u, c, v} J R).obj (ringedTensorUnitComplex.{c, v, u} J R, P) ≅ P,
      (∀ (n : ℤ) (h : 0 + n = n) (U : Cᵒᵖ) (a : R.obj.obj U)
        (x : (P.X n).val.obj U),
        (l.hom.f n).val.app U (coefficientTensorGenerator.{u, c, v} J R
          (ringedTensorUnitComplex.{c, v, u} J R) P 0 n n h U
          (ringedTensorUnitSection.{c, v, u} J R U a) x) =
        a • x) ∧
      (tensorIso (ringedTensorUnitComplex.{c, v, u} J R) P (Or.inr hP)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R),
            DerivedCategory.Q.obj P))
          (Y := (S.monoidal.tensorUnit, DerivedCategory.Q.obj P)) (unitIso.inv, 𝟙 _) ≫
        (S.monoidal.leftUnitor (DerivedCategory.Q.obj P)).hom =
      DerivedCategory.Q.map l.hom

/-- The right unitor is the corresponding coefficient multiplication.
Source: Stacks 0FPT and the signed total tensor of 06YN
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
def RingedDerivedTensorRightUnitorModel
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (tensorIso : RingedDerivedTensorComparison.{c, v, u, w} J R S)
    (unitIso : S.monoidal.tensorUnit ≅
      DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)) : Prop :=
  ∀ P hP,
    ∃ r : (coefficientTotalTensor.{u, c, v} J R).obj (P, ringedTensorUnitComplex.{c, v, u} J R) ≅ P,
      (∀ (n : ℤ) (h : n + 0 = n) (U : Cᵒᵖ) (a : R.obj.obj U)
        (x : (P.X n).val.obj U),
        (r.hom.f n).val.app U (coefficientTensorGenerator.{u, c, v} J R
          P (ringedTensorUnitComplex.{c, v, u} J R) n 0 n h U x
          (ringedTensorUnitSection.{c, v, u} J R U a)) =
        a • x) ∧
      (tensorIso P (ringedTensorUnitComplex.{c, v, u} J R) (Or.inl hP)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj P,
            DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)))
          (Y := (DerivedCategory.Q.obj P, S.monoidal.tensorUnit)) (𝟙 _, unitIso.inv) ≫
        (S.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom =
      DerivedCategory.Q.map r.hom

/-- Representative normalization of the closed symmetric monoidal structure.
All maps below are the specified structural maps, rather than unrelated object isomorphisms.
`tensorIso` includes the one-K-flat representative description; its naturality and agreement
with the simultaneous K-flat model make it the extension of that fixed comparison.

Source: Stacks 0FPT, 08J9 and the usual signed total tensor of 06YN
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal). -/
structure RingedDerivedTensorCoherence
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal) where
  /-- Total tensor computes derived tensor whenever either factor is K-flat. -/
  tensorIso : RingedDerivedTensorComparison.{c, v, u, w} J R S
  /-- Agreement with the already recorded simultaneous K-flat comparison. -/
  tensorIso_both : RingedDerivedTensorBothModel.{c, v, u, w} J R S T tensorIso
  /-- Naturality on all allowed representatives, including quasi-isomorphisms. -/
  tensorIso_naturality : RingedDerivedTensorNaturality.{c, v, u, w} J R S tensorIso
  /-- The monoidal unit is the coefficient ring in degree zero. -/
  unitIso : S.monoidal.tensorUnit ≅ DerivedCategory.Q.obj (ringedTensorUnitComplex.{c, v, u} J R)
  /-- The symmetry is induced by the signed swap on every K-flat tensor model. -/
  symmetry_model : RingedDerivedTensorSymmetryModel.{c, v, u, w} J R S T β
  /-- Reassociation is induced by reassociation of pure-tensor summands, without a sign. -/
  associator_model : RingedDerivedTensorAssociatorModel.{c, v, u, w} J R S T tensorIso
  /-- The left unitor is multiplication by the degree-zero coefficient. -/
  leftUnitor_model : RingedDerivedTensorLeftUnitorModel.{c, v, u, w} J R S tensorIso unitIso
  /-- The right unitor is the corresponding coefficient multiplication. -/
  rightUnitor_model : RingedDerivedTensorRightUnitorModel.{c, v, u, w} J R S tensorIso unitIso

/-- Retain the native identifications of the existing closed symmetric monoidal witness.
The construction is exactly the native tensor, comparison and Koszul symmetry used
by `ringedDerived_closed_symmetric_monoidal`; its forgetful public statement follows below. -/
private theorem ringedDerived_closed_symmetric_monoidal_native :
    ∃ S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R),
      S.monoidal = RingedDerivedNative.monoidal.{c, v, u, w} J R ∧
      ∃ T : CoefficientTensorModels.{u, c, v, w} J R S,
        ∃ β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
          _ S.monoidal,
        ∃ _hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β,
          HEq β (RingedDerivedNative.symmetric.{c, v, u, w} J R) ∧
          (∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
            (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
            HEq (T.iso J R S P Q hP hQ)
              (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP))) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨⟨m, adj, ev⟩, hm, T, hT⟩ :=
      RingedDerivedNative.closedAdjunction.{c, v, u, w} J R
    dsimp only [CoefficientClosedStructure.monoidal] at hm
    subst m
    let S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R) :=
      ⟨RingedDerivedNative.monoidal.{c, v, u, w} J R, adj, ev⟩
    let : MonoidalCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R)) :=
      RingedDerivedNative.monoidal.{c, v, u, w} J R
    let : SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R)) :=
      RingedDerivedNative.symmetric.{c, v, u, w} J R
    let : (DerivedCategory.Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ ⥤
        DerivedCategory (RingedTensorModules.{c, v, u} J R)).LaxMonoidal :=
      RingedDerivedNative.lax.{c, v, u, w} J R
    have ht : T.comparison = RingedDerivedNative.comparison.{c, v, u, w} J R :=
      eq_of_heq hT
    have htensor : ∀ P Q hP hQ,
        T.iso J R S P Q hP hQ =
          RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP) := by
      intro P Q hP hQ
      unfold CoefficientTensorModels.iso
      rw [ht]
      exact RingedDerivedNative.comparison_app.{c, v, u, w} J R ⟨P, hP⟩ ⟨Q, hQ⟩
    have hc := RingedDerivedNative.complexConstraints.{c, v, u} J R
    refine ⟨S, rfl, T, RingedDerivedNative.symmetric.{c, v, u, w} J R, {
      tensorIso := RingedDerivedNative.tensorIso.{c, v, u, w} J R
      tensorIso_both := ?_
      tensorIso_naturality := RingedDerivedNative.tensorIso_naturality.{c, v, u, w} J R
      unitIso := RingedDerivedNative.unitIso.{c, v, u, w} J R
      symmetry_model := ?_
      associator_model := ?_
      leftUnitor_model := ?_
      rightUnitor_model := ?_ }, HEq.rfl, (fun P Q hP hQ ↦ heq_of_eq (htensor P Q hP hQ))⟩
    · intro P Q hP hQ
      exact (htensor P Q hP hQ).symm
    · intro P Q hP hQ
      refine ⟨β_ P Q, hc.symmetry P Q, ?_⟩
      rw [htensor P Q hP hQ, htensor Q P hQ hP]
      exact RingedDerivedNative.symmetry_square.{c, v, u, w} J R P Q hP hQ
    · intro P Q N hP hQ hN
      refine ⟨MonoidalCategory.associator P Q N, hc.associator P Q N, ?_⟩
      rw [htensor P Q hP hQ, htensor Q N hQ hN]
      exact RingedDerivedNative.associator_square.{c, v, u, w} J R P Q N hP hQ hN
    · intro P hP
      refine ⟨MonoidalCategory.leftUnitor P, ?_, ?_⟩
      · exact hc.leftUnitor P
      · exact RingedDerivedNative.leftUnitor_square.{c, v, u, w} J R P hP
    · intro P hP
      refine ⟨MonoidalCategory.rightUnitor P, ?_, ?_⟩
      · exact hc.rightUnitor P
      · exact RingedDerivedNative.rightUnitor_square.{c, v, u, w} J R P hP

/-- The unbounded derived category of modules on a small ringed site is closed symmetric
monoidal, with its total-tensor constraints, Koszul symmetry and evaluation adjunction.

Source: Stacks 0FPT and 08J9
(blueprint: lem-sf-ringed-derived-closed-symmetric-monoidal).

Proof plan (the node's eleven steps):
1. Sheaf tensor is additive, closed and symmetric (`lem-pc-sheaf-modules-tensor-closed`);
   module sheaves have all colimits (`prop-pur-kinjective-resolutions-exist`). Apply
   `lem-sfb-total-tensor-homotopy` to totalize and descend through homotopies.
2. On bidegree (p,q), the signed swap has coefficient (-1)^(pq). Its differential commutes,
   its square is one and it is natural on chain maps and their homotopy classes.
3. K-flat complexes with flat terms contain the unit and are closed under total tensor:
   associate an acyclic test tensor and apply K-flatness twice; flat terms and their
   countable sums stay flat (`lem-pc-kflat-closure`).
4. Descend constraints and their inverses through the K-flat localization equivalence
   and unique extension of natural transformations (`lem-weil-pbc-site-derived-tensor-descent`).
5. Check pentagon, triangle and involutivity on representatives. Both hexagon paths have
   sign (-1)^(p(q+r)) = (-1)^(pq+pr), so the signed symmetry is symmetric monoidal.
6. Tensor commutes with cones; the cone criterion (`lem-pur-quasi-iso-cone-acyclic`), K-flat
   closure and `lem-pur-acyclic-kflat-tensor-arbitrary` give the one-K-flat comparison.
7. Choose K-flat sources (`lem-pc-kflat-resolution`) and a K-injective target
   (`prop-pur-kinjective-resolutions-exist`). Their Hom is K-injective
   (`lem-pur-hom-kflat-into-kinjective`); use `lem-weil-pbc-kinjective-hom-derived`.
8. Apply `lem-sc-derived-hom-tensor-total`, then global sections and ordinary H^0;
   `lem-pur-hom-complex-global-homotopy` identifies the tensor-Hom bijection.
9. Its inverse sends a curried map to x tensor y ↦ φ(x)(y), with no additional sign.
   The Hom differential gives exactly the chain-map and homotopy equations.
10. This formula is natural in all three complex variables; the localization and
    K-injective comparisons extend naturality to all derived morphisms.
11. Inverse transpose of the identity is resolved evaluation. Naturality in K gives
    uncurry(u) = (u tensor 1) followed by evaluation, the adjunction counit formula.

`CoefficientClosedStructure` retains all-variable naturality and the counit; its adjunction
Hom equivalence is the displayed bijection. `CoefficientTensorModels.uncurry_model` fixes
its evaluation normalization. `SymmetricCategory` retains naturality, involution and both
hexagons, and `MonoidalCategory` retains pentagon and triangle. No boundedness is assumed. -/
theorem ringedDerived_closed_symmetric_monoidal :
    ∃ S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R),
      ∃ T : CoefficientTensorModels.{u, c, v, w} J R S,
        ∃ β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
          _ S.monoidal,
          Nonempty (RingedDerivedTensorCoherence.{c, v, u, w} J R S T β) := by
  obtain ⟨S, _, T, β, hc, _, _⟩ :=
    ringedDerived_closed_symmetric_monoidal_native.{c, v, u, w} J R
  exact ⟨S, T, β, ⟨hc⟩⟩

end CategoryTheory
