/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientPullback
public import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
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
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.AlgebraicGeometry.CoefficientTensorChain.ProEtaleCoefficientTensorIso
import all WeilConjectures.AlgebraicGeometry.CoefficientTensorChain.ProEtaleCoefficientOrdinaryTensorSquare
import WeilConjectures.Algebra.Homology.ProperBaseChange.TensorTotalComparisonSquare

/-! # The chain square for change of coefficient isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

attribute [local irreducible] ordinaryPullback proEtaleOrdinaryTensorPullback
  proEtaleRingModulePullback

private theorem total_summand (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    CochainComplex.ιMapBifunctor
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P)
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)
        (proEtaleOrdinaryTensor X S) a b n h ≫
        ((proEtaleTensorPullbackTotalIso f R S c P Q).hom.f n) =
      (proEtaleOrdinaryTensorPullback f R S c (P.X a) (Q.X b)).inv ≫
        (proEtaleRingModulePullback f R S c).map
          (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor Y R) a b n h) := by
  dsimp only [proEtaleTensorPullbackTotalIso, asIso_hom,
    proEtaleTensorPullbackTotal, tensorPullbackTotal, tensorPullbackTotalComponent]
  exact HomologicalComplex.ι_mapBifunctorDesc _ _ _ _

attribute [local irreducible] tensorIso complexPullback proEtaleTensorPullbackTotalIso

-- Elaborate the three termwise tensor comparisons with their coefficient universes.
/-- The normalized restriction tensor map commutes with ordinary geometric tensor
pullback, as an equality of chain maps before localization.

Source: Stacks, Modules on Sites, Tag 03EL, its universal bilinear-map proof;
Cohomology on Sites, Tag 07A4, signed direct-sum totalization.
(blueprint: lem-pbc-coefficient-restriction-tensor-chain-square)

Proof: the supplied ring-isomorphism transport is normalized on pure tensors by
its pure_hom field and on each totalization summand by its total_summand field.
Precompose both sides in each total degree with each bidegree coproduct injection.
Use total_summand for the restriction map and the signed-total definition of each
geometric tensor pullback comparison. It remains to compare module sheaf maps.
Precompose with the sheafification unit and use the adjunction-unit normalization
of the geometric tensor pullbacks and ordinaryPullback. Both maps send a generalized
pure tensor to the same pair of inverse-image sections with scalar action changed
by c. TensorProduct.ext proves equality on presheaf tensors; the sheafification
adjunction then gives equality on sheaf tensors. Scalar restriction along c is an
equivalence and preserves these coproducts. Their universal property proves equality
of the degree maps, and extensionality gives the equality of chain maps. No derived
tensor model, localization or flatness assumption enters this calculation. The proof
also applies to zero coefficients, zero complexes, empty sites, and c equal to the
identity: it uses only tensor and coproduct universal properties. -/
theorem restriction_tensor_chain_square (o : SheafOfModules.RingIsoTensorTransport
    (J := ProEt.topology X)
    (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c) :
    ∀ P Q : CochainComplex (proEtaleRingModules Y R) ℤ,
        (complexPullback f R S c).hom.app ((total Y R).obj (P, Q)) ≫
            (proEtaleTensorPullbackTotalIso f R
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
              (Iso.refl _) P Q).inv =
          ((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).map
              (proEtaleTensorPullbackTotalIso f R S c P Q).inv ≫
            (tensorIso f R S c o).hom.app
              (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P,
                ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q) ≫
            (total X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).map
              (Prod.mkHom ((complexPullback f R S c).hom.app P)
                ((complexPullback f R S c).hom.app Q)) := by
  intro P Q
  let U := pbcRestrict c.hom
  have : U.IsEquivalence := by
    change (SheafOfModules.scalarRestriction c.hom).IsEquivalence
    rw [← o.functor_eq]
    infer_instance
  exact HomologicalComplex.tensorTotalComparisonSquare
    (proEtaleRingModulePullback f R S c) U
    (proEtaleRingModulePullback f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    (proEtaleOrdinaryTensor Y R) (proEtaleOrdinaryTensor X S)
    (proEtaleOrdinaryTensor X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (ordinaryPullback f R S c) (complexPullback f R S c)
    (complex_component f R S c)
    (proEtaleOrdinaryTensorPullback f R S c)
    (proEtaleOrdinaryTensorPullback f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    (proEtaleTensorPullbackTotalIso f R S c)
    (proEtaleTensorPullbackTotalIso f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    (total_summand f R S c)
    (total_summand f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    o.monoidal.toMonoidal.toOplaxMonoidal.δ (tensorIso f R S c o)
    (tensorIso_summand f R S c o)
    (ordinary_bifunctor_square f R S c o) P Q

/-- Localization of the normalized chain square.
Source: functoriality of localization, Stacks Tag 07A4.
(blueprint: lem-pbc-coefficient-restriction-tensor-chain-square) -/
theorem restriction_tensor_localized_square
    (o : SheafOfModules.RingIsoTensorTransport (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    DerivedCategory.Q.map ((complexPullback f R S c).hom.app ((total Y R).obj (P, Q))) ≫
      DerivedCategory.Q.map (proEtaleTensorPullbackTotalIso f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) P Q).inv =
    DerivedCategory.Q.map (((pbcRestrict c.hom).mapHomologicalComplex (.up ℤ)).map
      (proEtaleTensorPullbackTotalIso f R S c P Q).inv) ≫
      DerivedCategory.Q.map ((tensorIso f R S c o).hom.app
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P,
          ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      DerivedCategory.Q.map
        ((total X ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).map
          (Prod.mkHom ((complexPullback f R S c).hom.app P)
            ((complexPullback f R S c).hom.app Q))) := by
  simpa only [Functor.map_comp] using congrArg DerivedCategory.Q.map
    (restriction_tensor_chain_square f R S c o P Q)

end AlgebraicGeometry.Scheme.CoefficientTensorChain
