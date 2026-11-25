/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Ambient ringed pro-etale exchange

## Main definitions

- `proEtaleCanonicalDerivedPullbackComparison`: composition comparison with its
  normalized ordinary and K-flat representative characterizations retained.
- `proEtaleAmbientRingedExchange`: the mate of the comparison around the square.

## References

* Stacks Project, Lemma 0D6D
* Stacks Tags 07A7 and 0D6D

## Implementation details

`proEtaleCanonicalDerivedPullbackComparison` is chosen from the derived pullback composition
theorem together with its K-flat normalization; K-flat resolutions determine it on every
derived object. `proEtaleAmbientRingedExchange` is the construction of Stacks, Remark 07A7,
before any completeness or constructibility conditions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical derived pullback comparison `L(h ≫ k)^* ≅ Lk^* ⋙ Lh^*` for ringed pro-etale
sites, normalized on K-flat representatives. -/
noncomputable def proEtaleCanonicalDerivedPullbackComparison
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (R_V : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (R_W : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (R_Z : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c_k : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj R_V ≅ R_W)
    (c_h : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R_W ≅ R_Z) :
    proEtaleRingDerivedPullback (h ≫ k) R_V R_Z
        (proEtaleRingCompositeCoefficients h k R_V R_W R_Z c_k c_h) ≅
      proEtaleRingDerivedPullback k R_V R_W c_k ⋙
        proEtaleRingDerivedPullback h R_W R_Z c_h := by
  let c_hk := proEtaleRingCompositeCoefficients h k R_V R_W R_Z c_k c_h
  have hex : ∃ (c : proEtaleRingDerivedPullback (h ≫ k) R_V R_Z c_hk ≅
                proEtaleRingDerivedPullback k R_V R_W c_k ⋙
                  proEtaleRingDerivedPullback h R_W R_Z c_h),
    ∃ (adj_k : proEtaleRingModulePullback k R_V R_W c_k ⊣
          proEtaleRingModuleDirectImage k R_V R_W c_k)
      (adj_h : proEtaleRingModulePullback h R_W R_Z c_h ⊣
          proEtaleRingModuleDirectImage h R_W R_Z c_h)
      (adj_hk : proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk ⊣
          proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk),
      proEtaleRingModuleAdjunctionNormalized k R_V R_W c_k adj_k ∧
      proEtaleRingModuleAdjunctionNormalized h R_W R_Z c_h adj_h ∧
      proEtaleRingModuleAdjunctionNormalized (h ≫ k) R_V R_Z c_hk adj_hk ∧
      ∃ (d : proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
            proEtaleRingModuleDirectImage k R_V R_W c_k ≅
              proEtaleRingModuleDirectImage (h ≫ k) R_V R_Z c_hk),
        (∀ (N : proEtaleRingModules Z R_Z) (U : V.ProEt)
            (m : ((proEtaleRingModuleDirectImage h R_W R_Z c_h ⋙
              proEtaleRingModuleDirectImage k R_V R_W c_k).obj N).val.obj (Opposite.op U)),
          (d.hom.app N).val.app (Opposite.op U) m =
            N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m) ∧
        ∃ (a : proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk ≅
              proEtaleRingModulePullback k R_V R_W c_k ⋙
                proEtaleRingModulePullback h R_W R_Z c_h),
          conjugateIsoEquiv (adj_k.comp adj_h) adj_hk a = d ∧
          ∃ (b : (proEtaleRingModulePullback (h ≫ k) R_V R_Z c_hk).mapHomologicalComplex
                (ComplexShape.up ℤ) ≅
              (proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                (ComplexShape.up ℤ) ⋙
              (proEtaleRingModulePullback h R_W R_Z c_h).mapHomologicalComplex
                (ComplexShape.up ℤ)),
            (∀ (K : CochainComplex (proEtaleRingModules V R_V) ℤ) (n : ℤ),
              (b.hom.app K).f n = a.hom.app (K.X n)) ∧
              ∀ (K : CochainComplex (proEtaleRingModules V R_V) ℤ),
                CochainComplex.IsAcyclicTensorKFlat K →
                (∀ n : ℤ,
                  SheafOfModules.IsFlatOnSite (J := ProEt.topology V) (R := R_V) (K.X n)) →
                CochainComplex.IsAcyclicTensorKFlat
                  (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K) ∧
                (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W) (R := R_W)
                  ((((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj K).X n)) ∧
                (proEtaleRingDerivedPullbackFactors (h ≫ k) R_V R_Z c_hk).hom.app K ≫
                    DerivedCategory.Q.map (b.hom.app K) =
                  c.hom.app (DerivedCategory.Q.obj K) ≫
                    (proEtaleRingDerivedPullback h R_W R_Z c_h).map
                      ((proEtaleRingDerivedPullbackFactors k R_V R_W c_k).hom.app K) ≫
                    (proEtaleRingDerivedPullbackFactors h R_W R_Z c_h).hom.app
                      (((proEtaleRingModulePullback k R_V R_W c_k).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj K) := by
    have H := proEtaleRingDerivedPullbackComposition h k R_V R_W R_Z c_k c_h c_hk rfl
    rcases H with ⟨adj_k, adj_h, adj_hk, nk, nh, nhk, d, hd, a, ha, b, hb, c, hc⟩
    exact ⟨c, adj_k, adj_h, adj_hk, nk, nh, nhk, d, hd, a, ha, b, hb, hc⟩
  exact hex.choose

/-- The canonical pullback comparison around the coefficient-compatible square.
This exposes the exact comparison whose mate defines ambient exchange. -/
noncomputable def proEtaleAmbientRingedPullbackComparison
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (R_Y' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R_Y ≅ R_Y')
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj R_X ≅ R_X')
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj R_Y' ≅ R_X')
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g')
      (proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f'))
    : proEtaleRingDerivedPullback g R_Y R_Y' c_g ⋙
        proEtaleRingDerivedPullback f' R_Y' R_X' c_f' ≅
      proEtaleRingDerivedPullback f R_Y R_X c_f ⋙
        proEtaleRingDerivedPullback g' R_X R_X' c_g' := by
  let theta_left :=
    (proEtaleCanonicalDerivedPullbackComparison f' g R_Y R_Y' R_X' c_g c_f').symm
  let theta_right :=
    proEtaleCanonicalDerivedPullbackComparison g' f R_Y R_X R_X' c_f c_g'
  let c_fg : (proEtaleSheafInverseImage (f' ≫ g) CommRingCat.{u + 1}).obj R_Y ≅ R_X' :=
    proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f'
  let P : Σ q : X' ⟶ Y,
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj R_Y ≅ R_X' :=
    ⟨f' ≫ g, c_fg⟩
  let Q : Σ q : X' ⟶ Y,
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj R_Y ≅ R_X' :=
    ⟨g' ≫ f, proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g'⟩
  have hPQ : P = Q := by
    apply Sigma.ext sq.toCommSq.w.symm
    exact hcoeff.symm
  let F := fun z : (Σ q : X' ⟶ Y,
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj R_Y ≅ R_X') ↦
    proEtaleRingDerivedPullback z.1 R_Y R_X' z.2
  have hfun := congrArg F hPQ
  let theta_left' :
      proEtaleRingDerivedPullback g R_Y R_Y' c_g ⋙
          proEtaleRingDerivedPullback f' R_Y' R_X' c_f' ≅
        proEtaleRingDerivedPullback (g' ≫ f) R_Y R_X'
          (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g') :=
    theta_left ≪≫ eqToIso hfun
  exact theta_left' ≪≫ theta_right

/-- The ambient exchange map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` for a cartesian square of ringed
pro-etale sites, with `hcoeff` recording that the two composite coefficient identifications
agree: the mate of the canonical derived pullback comparison under the derived
pullback/direct image adjunctions. -/
noncomputable def proEtaleAmbientRingedExchange
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (R_Y' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R_Y ≅ R_Y')
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj R_X ≅ R_X')
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj R_Y' ≅ R_X')
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g')
      (proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f'))
    :
    proEtaleRingDerivedDirectImage f R_Y R_X c_f ⋙
          proEtaleRingDerivedPullback g R_Y R_Y' c_g ⟶
        proEtaleRingDerivedPullback g' R_X R_X' c_g' ⋙
          proEtaleRingDerivedDirectImage f' R_Y' R_X' c_f' :=
  (mateEquiv (proEtaleRingDerivedAdjunction f R_Y R_X c_f)
    (proEtaleRingDerivedAdjunction f' R_Y' R_X' c_f')
    (TwoSquare.mk _ _ _ _
      (proEtaleAmbientRingedPullbackComparison sq R_X R_Y R_X' R_Y'
        c_f c_g c_g' c_f' hcoeff).hom))

end AlgebraicGeometry.Scheme
