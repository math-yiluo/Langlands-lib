/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Module.FinitePresentation
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackSupplement
public import WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.SixFunctors.LocallyFreeDerivedScalars
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension.ConstantMatrixCokernelModels
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all WeilConjectures.Algebra.Homology.Scalar.ScalarDualEvaluationDescent
import all WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ULift
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement

import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeCoefficientPullbackIso
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import all WeilConjectures.AlgebraicGeometry.LatticeClassDescent
import all WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
import all WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
import all WeilConjectures.AlgebraicGeometry.LatticePairRestriction
import all Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import all WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
import all WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
import all WeilConjectures.AlgebraicGeometry.LatticePairDescentData
import all WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverPreserving
import all Mathlib.CategoryTheory.Sites.CoversTop.Over
import all Mathlib.CategoryTheory.Sites.SheafHom
import all Mathlib.CategoryTheory.Sites.LocalProperties
import all WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
import all WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.LargeSetSheafification
import all WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import all WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import all WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
import all WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all Mathlib.LinearAlgebra.TensorProduct.Pi
import all Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import all Mathlib.LinearAlgebra.TensorProduct.Basis
import all WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import all Mathlib.Topology.Algebra.OpenSubgroup
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import all Mathlib.Topology.ContinuousMap.Algebra
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import all Mathlib.Analysis.Normed.Field.WithAbs
import all Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import all Mathlib.GroupTheory.Coset.Defs
import all Mathlib.Topology.Algebra.Module.Equiv.Basic
import all Mathlib.Topology.Algebra.Module.Equiv.Pi
import all Mathlib.Topology.CompactOpen
import all Mathlib.LinearAlgebra.Basis.Defs
import all WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.RingTheory.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement
import all Mathlib.LinearAlgebra.Dimension.Constructions
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.LinearAlgebra.TensorProduct.Map
import all WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.Algebra.Category.ModuleCat.Products
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.ConstantScalarTowerComparison

/-! # Rational finite free models on the original strata

## References

* Bhatt--Scholze, Lemma 6.8.2, the paragraph before Definition 6.8.6, Definition 6.8.10 and
  Proposition 6.8.14(2)
* Stacks, Tags 03EI, 03EK, 03EL and 03EP
* Bhatt--Scholze, Definition 6.8.1
* Bhatt--Scholze, Lemma 6.8.2
* Bhatt--Scholze, Definition 6.8.10
* Bhatt--Scholze, Definition 6.8.6
* Bhatt--Scholze, Proposition 6.8.14(2)
* Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
* Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.14(2)
* Bhatt--Scholze, Definition 6.8.6 and Proposition 6.8.14(2)
* Stacks, Section 03EK
* Bhatt--Scholze, paragraph before Definition 6.8.6
* Stacks 03EK and 0GMW
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
-- Repeated universe-polymorphic sheafification inference makes this linter expensive.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SheafOfModules
open AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ProEtale.RationalStratum

private instance stratumWeakAdd (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) AddCommGrpCat.{u + 1} := inferInstance

private instance stratumWeakRing (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) CommRingCat.{u + 1} := inferInstance

private instance stratumWeakNoncommRing (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) RingCat.{u + 1} := inferInstance

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Integral scalars in the module universe. -/
abbrev A := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- Rational scalars in the module universe. -/
abbrev K := ULift.{u + 1, u} E

/-- The ordinary inclusion of coefficient rings. -/
abbrev inclusion : A l E →+* K E :=
  RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype

/-- Integral constant sections, using the existing constant-sheaf comparison. -/
def integralConstants (S : Scheme.{u}) :
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).obj (CommRingCat.of (A l E)) ⟶
      integralCoefficientSheaf l S E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientConstantComparison S (A l E)

/-- Rational constant sections, using the existing constant-sheaf comparison. -/
def rationalConstants (S : Scheme.{u}) :
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).obj (CommRingCat.of (K E)) ⟶
      rationalCoefficientSheaf l S E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientConstantComparison S (K E)

/-- Ordinary rationalization `E tensor_A N`. -/
abbrev vectorSpace (N : ModuleCat.{u + 1} (A l E)) : ModuleCat.{u + 1} (K E) :=
  (ModuleCat.extendScalars (inclusion l E)).obj N

/-- The specified integral local model, with the recorded constant module functor. -/
abbrev integralModel (S : Scheme.{u}) (N : ModuleCat.{u + 1} (A l E)) :
    Modules (integralCoefficientSheaf l S E) :=
  ConstantFiniteFreePresentationExtension.extension (ProEt.topology S) (A l E)
    (integralCoefficientSheaf l S E) (integralConstants l E S) N

/-- Scalar extension from the completed integral coefficient sheaf. -/
abbrev rationalize (S : Scheme.{u}) (M : Modules (integralCoefficientSheaf l S E)) :
    Modules (rationalCoefficientSheaf l S E) :=
  changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (integralRationalCoefficientMap l E S) M

/-- The middle scalar model `E_S tensor_A N_S`. -/
abbrev directModel (S : Scheme.{u}) (N : ModuleCat.{u + 1} (A l E)) :
    Modules (rationalCoefficientSheaf l S E) :=
  ConstantFiniteFreePresentationExtension.extension (ProEt.topology S) (A l E)
    (rationalCoefficientSheaf l S E)
    (integralConstants l E S ≫ integralRationalCoefficientMap l E S) N

/-- The rational constant-module model `E_S tensor_E V_S`. -/
abbrev rationalModel (S : Scheme.{u}) (V : ModuleCat.{u + 1} (K E)) :
    Modules (rationalCoefficientSheaf l S E) :=
  ConstantFiniteFreePresentationExtension.extension (ProEt.topology S) (K E)
    (rationalCoefficientSheaf l S E) (rationalConstants l E S) V

/-- The normalized first comparison is the existing balanced scalar-tower isomorphism. -/
abbrev reassociation (S : Scheme.{u}) (N : ModuleCat.{u + 1} (A l E)) :
    rationalize l E S (integralModel l E S N) ≅ directModel l E S N :=
  scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1}
    (integralConstants l E S) (integralRationalCoefficientMap l E S)
    ((constantModuleHomFunctor (ProEt.topology S) (A l E)).obj N)

/-- Integral restriction with the canonical continuous pullback of coefficient rings. -/
def integralPullback {S X : Scheme.{u}} (h : S ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (integralCoefficientSheaf l X E) ⟶ integralCoefficientSheaf l S E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (A l E) h

/-- Rational restriction with the canonical continuous pullback of coefficient rings. -/
def rationalPullback {S X : Scheme.{u}} (h : S ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l X E) ⟶ rationalCoefficientSheaf l S E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback (K E) h

/-- The specified ordinary map from N to its rationalization, n mapped to 1 tensor n. -/
abbrev vectorUnit (N : ModuleCat.{u + 1} (A l E)) (x : N) : vectorSpace l E N :=
  (ModuleCat.ExtendRestrictScalarsAdj.Unit.map.{u + 1, u + 1, u + 1} (inclusion l E)) x

/-- The finite power of the rational coefficient sheaf, including rank zero. -/
abbrev freeModel (S : Scheme.{u}) (n : ℕ) : Modules (rationalCoefficientSheaf l S E) :=
  ConstantFiniteFreePresentationExtension.power.{u + 1, u} (ProEt.topology S)
    ((sheafCompose (ProEt.topology S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (rationalCoefficientSheaf l S E)) n

/-- Coordinates in the recorded finite power. -/
abbrev coord (S : Scheme.{u}) (n : ℕ) (U : S.ProEtᵒᵖ)
    (x : (freeModel l E S n).val.obj U) (i : Fin n) :=
  ConstantFiniteFreePresentationExtension.commCoordinate.{u + 1, u} (ProEt.topology S)
    (rationalCoefficientSheaf l S E) n U x i

/-- Direct scalar-model maps, using the constant-module functor recorded by the dependency. -/
abbrev directMap (S : Scheme.{u}) {N N' : ModuleCat.{u + 1} (A l E)} (f : N ⟶ N') :
    directModel l E S N ⟶ directModel l E S N' :=
  ConstantFiniteFreePresentationExtension.extensionMap (ProEt.topology S) (A l E)
    (rationalCoefficientSheaf l S E)
    (integralConstants l E S ≫ integralRationalCoefficientMap l E S) f

/-- Rational scalar-model maps. -/
abbrev rationalMap (S : Scheme.{u}) {V V' : ModuleCat.{u + 1} (K E)} (f : V ⟶ V') :
    rationalModel l E S V ⟶ rationalModel l E S V' :=
  ConstantFiniteFreePresentationExtension.extensionMap (ProEt.topology S) (K E)
    (rationalCoefficientSheaf l S E) (rationalConstants l E S) f

set_option backward.isDefEq.respectTransparency false in
private theorem constants_compatible (S : Scheme.{u}) (U : S.ProEtᵒᵖ) (r : A l E) :
    (scalarRingUnit (ProEt.topology S) (A l E) (rationalCoefficientSheaf l S E)
      (integralConstants l E S ≫ integralRationalCoefficientMap l E S)).app U r =
    (scalarRingUnit (ProEt.topology S) (K E) (rationalCoefficientSheaf l S E)
      (rationalConstants l E S)).app U (inclusion l E r) := by
  let := coefficientExtensionNormedField l E
  rw [scalarRingUnit_apply, scalarRingUnit_apply]
  change (integralRationalCoefficientMap l E S).hom.app U
      ((continuousCoefficientConstantComparison S (A l E)).hom.app U
        ((toSheafify (ProEt.topology S)
          ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (A l E)))).app U r)) = _
  have hA := congrArg (fun t ↦ t.app U r)
    (continuousCoefficientConstantComparison_unit S (A l E))
  have hK := congrArg (fun t ↦ t.app U (inclusion l E r))
    (continuousCoefficientConstantComparison_unit S (K E))
  change (continuousCoefficientConstantComparison S (A l E)).hom.app U
    ((toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (A l E)))).app U r) = _ at hA
  rw [hA]
  change _ = (continuousCoefficientConstantComparison S (K E)).hom.app U
    ((toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E)))).app U (inclusion l E r))
  rw [show (continuousCoefficientConstantComparison S (K E)).hom.app U
    ((toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E)))).app U (inclusion l E r)) =
    _ from hK]
  rfl

end Coefficients

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] GenericScalar.scalarModelIso GenericScalar.scalarForward
  GenericScalar.scalarBackward GenericScalar.scalarForwardRaw GenericScalar.scalarBackwardRaw
  GenericScalar.backwardUnit GenericScalar.backwardLinear

/-- Both normalized scalar identifications, natural in finitely presented N.
The first is the existing scalar-tower isomorphism, not an arbitrary isomorphism.
The second is normalized on all local constant-module sections by n mapped to 1 tensor n.
Its naturality equation and the restriction of both isomorphisms to every slice retain
any chosen covering object. -/
theorem scalarModels (S : Scheme.{u}) :
    ∃ e : ∀ (N : ModuleCat.{u + 1} (A l E)) (_hN : Module.FinitePresentation (A l E) N),
        directModel l E S N ≅ rationalModel l E S (vectorSpace l E N),
      (∀ (N : ModuleCat.{u + 1} (A l E)) (_hN : Module.FinitePresentation (A l E) N)
        (U : S.ProEtᵒᵖ)
        (x : ((constantModuleHomFunctor (ProEt.topology S) (A l E)).obj N).val.obj U)
        (b : (integralCoefficientSheaf l S E).obj.obj U)
        (a : (rationalCoefficientSheaf l S E).obj.obj U),
        (reassociation l E S N).hom.val.app U
          (scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            (integralRationalCoefficientMap l E S) (integralModel l E S N) U a
            (scalarExtensionSection.{u + 1, u, u + 1, u + 1}
              (integralConstants l E S) _ U b x)) =
          scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            (integralConstants l E S ≫ integralRationalCoefficientMap l E S) _ U
            (a * (integralRationalCoefficientMap l E S).hom.app U b) x) ∧
      (∀ (N : ModuleCat.{u + 1} (A l E)) (hN : Module.FinitePresentation (A l E) N)
        (U : S.ProEtᵒᵖ) (x : N) (a : (rationalCoefficientSheaf l S E).obj.obj U),
        (e N hN).hom.val.app U
          (scalarExtensionSection.{u + 1, u, u + 1, u + 1}
            (integralConstants l E S ≫ integralRationalCoefficientMap l E S) _ U a
            ((constantModuleHomUnit (ProEt.topology S) (A l E) N).app U x)) =
          scalarExtensionSection.{u + 1, u, u + 1, u + 1} (rationalConstants l E S) _ U a
            ((constantModuleHomUnit (ProEt.topology S) (K E) (vectorSpace l E N)).app U
              (vectorUnit l E N x))) ∧
      (∀ (N N' : ModuleCat.{u + 1} (A l E))
        (hN : Module.FinitePresentation (A l E) N)
        (hN' : Module.FinitePresentation (A l E) N') (f : N ⟶ N'),
        directMap l E S f ≫ (e N' hN').hom =
          (e N hN).hom ≫ rationalMap l E S ((ModuleCat.extendScalars (inclusion l E)).map f)) ∧
      (∀ (N : ModuleCat.{u + 1} (A l E)) (hN : Module.FinitePresentation (A l E) N)
        (U : S.ProEt),
        Nonempty ((rationalize l E S (integralModel l E S N)).over U ≅
          (rationalModel l E S (vectorSpace l E N)).over U)) := by
  obtain ⟨e, he, hn⟩ := GenericScalar.scalarModel_spec (constants_compatible l E S)
  refine ⟨fun N _ ↦ e N, ?_, ?_, ?_, ?_⟩
  · intro N _hN U x b a
    dsimp only [reassociation]
    rw [scalarExtensionTowerIso_hom.{u + 1, u, u + 1, u + 1}]
    exact scalarExtensionTowerForward_tmul.{u + 1, u, u + 1, u + 1}
      (integralConstants l E S) (integralRationalCoefficientMap l E S)
      ((constantModuleHomFunctor (ProEt.topology S) (A l E)).obj N) U a b x
  · intro N hN U x a
    exact he N U a x
  · intro N N' hN hN' f
    exact hn f
  · intro N hN U
    exact ⟨(overFunctor.{u + 1} _ U).mapIso
      (reassociation l E S N ≪≫ e N)⟩

attribute [local irreducible] Scheme.PurScalar.scalarIso proEtaleModuleInverseImage
attribute [local irreducible] scalarExtensionSection
  changeOfRingsHomOfUniverses

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientSquare {S X : Scheme.{u}} (h : S ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (integralRationalCoefficientMap l E X) ≫ rationalPullback l E h =
      integralPullback l E h ≫ integralRationalCoefficientMap l E S := by
  let := coefficientExtensionNormedField l E
  exact continuousCoefficientPullback_naturality (inclusion l E)
    (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)) h

end Coefficients

section
namespace GenericTowers
variable {D : Type (u + 1)} [Category.{u} D] {J : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
private abbrev Rings := Sheaf J CommRingCat.{u + 1}
private abbrev Modules (R : Sheaf J CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
end GenericTowers
end

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The lattice presentation of rational continuous coefficients with their prescribed norm. -/
def rationalLatticeRing (X : Scheme.{u}) : Rings X := by
  letI := coefficientExtensionNormedField l E
  exact latticeCoefficientSheaf X E

/-- Commute continuous functions with the universe lift, by the pointwise maps.
This transports to the coefficient presentation used by the recorded constructibility notion. -/
def rationalLatticeRingIso (X : Scheme.{u}) :
    rationalCoefficientSheaf l X E ≅ rationalLatticeRing l E X := by
  letI := coefficientExtensionNormedField l E
  exact
    { hom := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ULift.up
              ⟨fun x ↦ (f x).down, continuous_uliftDown.comp f.continuous⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦
              ⟨fun x ↦ ULift.up (f.down x), continuous_uliftUp.comp f.down.continuous⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by ext V f; rfl
      inv_hom_id := by ext V f; rfl }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
private def constantComparison (S : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    (N : ModuleCat.{u + 1} R) :
    (adicLisseConstantModules S R).obj N ≅
      (constantModuleHomFunctor (ProEt.topology S) R).obj N := by
  let J := ProEt.topology S
  let η := toSheafify J ((Functor.const S.ProEtᵒᵖ).obj (RingCat.of R))
  let θ := adicLisseConstantUnit S R
  let c := (constantModuleHomRingIso J R).inv
  have hs : θ ≫ c.hom = η := by
    apply (cancel_mono (constantModuleHomRingIso J R).hom.hom).mp
    rw [Category.assoc]
    change θ ≫ ((constantModuleHomRingIso J R).inv ≫
      (constantModuleHomRingIso J R).hom).hom = _
    rw [Iso.inv_hom_id]
    change θ ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (sheafComposeNatTrans_fac J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      (sheafificationAdjunction J CommRingCat.{u + 1})
      (sheafificationAdjunction J RingCat.{u + 1})
      ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of R))).symm
  let P := (siteConstantModulePresheafGeneral (C := S.ProEt) R).obj N
  let f := moduleSheafificationComparison J θ η c hs P
  have : IsIso f := moduleSheafificationComparison_isIso J θ η c hs P
  exact asIso f

private def scalarTransport (S : Scheme.{u}) {R T B : Rings S}
    (a : R ⟶ T) (b : R ⟶ B) (e : T ≅ B) (he : a ≫ e.hom = b)
    (M : Modules R) :
    changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} b M ≅
      (restrictScalars ((sheafCompose (ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.inv)).obj
        (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M) := by
  let J := ProEt.topology S
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let t := coefficientTensorPresheafIso.{u} J b a (Iso.refl R) e he M
  exact (PresheafOfModules.sheafification.{u + 1} (R := F.obj B) (𝟙 _)).mapIso t ≪≫
    pushforwardSheafificationIso.{u} J J (𝟭 S.ProEt) (F.obj T) (F.obj B)
      (F.map e.inv) (changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} a M)

private theorem constantSquare (S : Scheme.{u}) :
    letI := coefficientExtensionNormedField l E
    rationalConstants l E S ≫ (rationalLatticeRingIso l E S).hom =
      continuousCoefficientConstantMap S E := by
  let := coefficientExtensionNormedField l E
  let J := ProEt.topology S
  let adj := sheafificationAdjunction J CommRingCat.{u + 1}
  apply (adj.homEquiv _ _).injective
  change toSheafify J ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E))) ≫
    ((rationalConstants l E S) ≫ (rationalLatticeRingIso l E S).hom).hom = _
  change (toSheafify J ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E))) ≫
    (rationalConstants l E S).hom) ≫ (rationalLatticeRingIso l E S).hom.hom = _
  change (toSheafify (ProEt.topology S)
    ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E))) ≫
      (continuousCoefficientConstantComparison S (K E)).hom) ≫ _ = _
  rw [continuousCoefficientConstantComparison_unit S (K E)]
  change _ = (adj.homEquiv
    ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E)))
    (latticeCoefficientSheaf S E))
    ((adj.homEquiv ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (K E)))
      (latticeCoefficientSheaf S E)).symm
        (AlgebraicGeometry.ProEtale.continuousCoefficientConstants S E))
  rw [Equiv.apply_symm_apply]
  rfl

end Coefficients
end AlgebraicGeometry.ProEtale.RationalStratum
