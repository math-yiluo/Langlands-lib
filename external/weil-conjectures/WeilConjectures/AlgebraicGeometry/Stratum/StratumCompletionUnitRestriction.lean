/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackInterface
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonFormula
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionNormalizationScalarMate
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.RestrictionPullbackScalarComposition
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.ProductPreservingDerivedLimitMate
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionAugmentationCompatibility
import all WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateRestrictionCounitRoute
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.CategoryTheory.StrictReduction.ReductionPullbackDerivedTower
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import all WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import all Mathlib.CategoryTheory.Limits.Preserves.Finite
import all WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import all Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import all WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.CategoryTheory.Sites.RegularEpi
import all Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.InverseMateEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import all Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.Mathlib.CategoryTheory.NatIso
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-!
# Restriction of the quotient completion unit and finite-stratum detection

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.5.8(1),(2)
and Proposition 6.6.11, reverse implication; Stacks Tags 03EL, 0941, 099M, 0A0E
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).

The coefficient rings, reduction functors, quotient normalizations and completion
unit are the published constructions. Positive level n means exponent n+1.
The ordinary tower comparison is fixed by the quotient augmentation. Its derived
comparison is fixed on K-flat representatives by the universal reduction counits.
The inverse-limit map is the mate of the constant-tower comparison. Thus the
completion comparison includes its specified map from the restricted object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry.Scheme

/-- The restrictions in the statement: a locally closed immersion, a site-object
restriction, or either order of their composite. A weakly etale morphism is exactly
an object of the small pro-etale site over its target.
Source: Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def IsAdicStratumRestriction {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IsImmersion f ∨ WeaklyEtale f ∨
    (∃ (Z : Scheme.{u}) (i : Z ⟶ X) (j : Y ⟶ Z),
      IsImmersion i ∧ WeaklyEtale j ∧ j ≫ i = f) ∨
    (∃ (Z : Scheme.{u}) (j : Z ⟶ X) (i : Y ⟶ Z),
      WeaklyEtale j ∧ IsImmersion i ∧ i ≫ j = f)

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual module inverse image with the canonical completed coefficient transport.
Source: Bhatt--Scholze, Lemma 6.5.8(1)
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
abbrev stratumModulePull :=
  proEtaleRingModulePullback f (d.completedRing X) (d.completedRing Y) (d.integralRingIso f)

section
attribute [local irreducible] HasDerivedCategory.standard

private theorem isoOfEpiAugmentations
    {C D J : Type*} [Category C] [Category D] [Category J]
    (U R S : C ⥤ J ⥤ D) (α : U ⟶ R) (β : U ⟶ S)
    (hα : ∀ M n, Epi ((α.app M).app n))
    (he : ∀ M n, ∃ e : (R.obj M).obj n ≅ (S.obj M).obj n,
      (α.app M).app n ≫ e.hom = (β.app M).app n) :
    ∃! e : R ≅ S, ∀ M, α.app M ≫ e.hom.app M = β.app M := by
  classical
  choose e he using he
  let eM (M : C) : R.obj M ≅ S.obj M := NatIso.ofComponents (e M) (by
    intro m n g
    let := hα M m
    apply (cancel_epi ((α.app M).app m)).1
    calc
      (α.app M).app m ≫ (R.obj M).map g ≫ (e M n).hom =
          (U.obj M).map g ≫ (α.app M).app n ≫ (e M n).hom := by
        rw [← Category.assoc, ← (α.app M).naturality g, Category.assoc]
      _ = (U.obj M).map g ≫ (β.app M).app n := by rw [he]
      _ = (β.app M).app m ≫ (S.obj M).map g := (β.app M).naturality g
      _ = (α.app M).app m ≫ (e M m).hom ≫ (S.obj M).map g := by
        rw [← he, Category.assoc])
  let e' : R ≅ S := NatIso.ofComponents eM (by
    intro M N g
    ext n
    let := hα M n
    apply (cancel_epi ((α.app M).app n)).1
    have hαg := NatTrans.congr_app (α.naturality g) n
    have hβg := NatTrans.congr_app (β.naturality g) n
    change (U.map g).app n ≫ (α.app N).app n =
      (α.app M).app n ≫ (R.map g).app n at hαg
    change (U.map g).app n ≫ (β.app N).app n =
      (β.app M).app n ≫ (S.map g).app n at hβg
    change (α.app M).app n ≫ (R.map g).app n ≫ (e N n).hom =
      (α.app M).app n ≫ (e M n).hom ≫ (S.map g).app n
    rw [← Category.assoc, ← hαg, Category.assoc, he, ← Category.assoc, he]
    exact hβg)
  have he' (M) : α.app M ≫ e'.hom.app M = β.app M := by
    ext n
    exact he M n
  refine ⟨e', he', ?_⟩
  intro e'' he''
  apply Iso.ext
  ext M n
  let := hα M n
  apply (cancel_epi ((α.app M).app n)).1
  exact (NatTrans.congr_app (he'' M) n).trans
    (NatTrans.congr_app (he' M) n).symm

private theorem stratumModuleUnit_component (T : Scheme.{u})
    (M : reductionModules T (d.completedRing T)) (n : ℕ) :
    ((completedReductionModuleUnit d T).app M).app (op n) =
      (pbcScalarAdjunction (d.projection T n)).unit.app M := by
  ext U x
  exact ((completedReductionModuleUnit_exists d T).exists.choose_spec M n U x).trans
    ((pbcScalarAdjunction_exists (d.projection T n)).exists.choose_spec M U x).symm

private theorem stratumModuleUnit_epi (T : Scheme.{u})
    (M : reductionModules T (d.completedRing T)) (n : ℕ) :
    Epi (((completedReductionModuleUnit d T).app M).app (op n)) := by
  rw [actualReductionUnit_component]
  exact comparisonChangeUnit_epi T _ (completedProjection_surjective T d n) M

/-- The ordinary inverse scalar mate, with its unit normalization. -/
private theorem stratumScalarIso_exists (n : ℕ) :
    ∃ e : proEtaleRingExtension (d.projection X n) ⋙
        proEtaleRingModulePullback f (d.finiteRing X n) (d.finiteRing Y n)
          (d.finiteRingIso f n) ≅
        stratumModulePull d f ⋙ proEtaleRingExtension (d.projection Y n),
      ∀ M, (stratumModulePull d f).map
          ((pbcScalarAdjunction (d.projection X n)).unit.app M) ≫
        (proEtaleRingRestrictionPullbackInv f
          (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
          (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
          (d.projection_comm f n)).app ((proEtaleRingExtension (d.projection X n)).obj M) ≫
        (proEtaleRingRestrictScalars (d.projection Y n)).map (e.hom.app M) =
      (pbcScalarAdjunction (d.projection Y n)).unit.app ((stratumModulePull d f).obj M) := by
  let av := proEtaleRingExtensionAdjunction (d.projection X n)
  let au := proEtaleRingExtensionAdjunction (d.projection Y n)
  let ar := proEtaleRingModuleAdjunction f (d.completedRing X) (d.completedRing Y)
    (d.integralRingIso f)
  let az := proEtaleRingModuleAdjunction f (d.finiteRing X n) (d.finiteRing Y n)
    (d.finiteRingIso f n)
  let b := proEtaleRingRestrictionPullbackInv f
    (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
    (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
    (d.projection_comm f n)
  let t := proEtaleRingRestrictionDirectImage f
    (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
    (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
    (d.projection_comm f n)
  let β := TwoSquare.mk _ _ _ _ b
  have hm : mateEquiv az ar β = t.hom :=
    restrictionPullback_mate f _ _ _ _ _ _ _ _ _
  let γ := (mateEquiv av au).symm β
  have hγ : IsIso γ := by
    have hmate : mateEquiv av au γ = β := Equiv.apply_symm_apply _ _
    have : IsIso (conjugateEquiv (av.comp az) (ar.comp au) γ) := by
      rw [← iterated_mateEquiv_conjugateEquiv av au ar az γ, hmate, hm]
      infer_instance
    exact conjugateEquiv_of_iso (av.comp az) (ar.comp au) γ
  let e := (asIso γ).symm
  refine ⟨e, ?_⟩
  intro M
  have h := unit_mateEquiv_symm av au β M
  change (stratumModulePull d f).map (av.unit.app M) ≫ b.app _ ≫
    (proEtaleRingRestrictScalars (d.projection Y n)).map (e.hom.app M) = _
  rw [← Category.assoc]
  have hh := (Iso.comp_inv_eq
    ((proEtaleRingRestrictScalars (d.projection Y n)).mapIso ((asIso γ).app M))).2 h
  exact hh

private theorem stratumModuleLevelIso (n : ℕ)
    (M : reductionModules X (d.completedRing X)) :
    ∃ e : (stratumModulePull d f).obj ((completedReductionLevel X d n).obj M) ≅
        (completedReductionLevel Y d n).obj ((stratumModulePull d f).obj M),
      (stratumModulePull d f).map
          (((completedReductionModuleUnit d X).app M).app (op n)) ≫ e.hom =
        ((completedReductionModuleUnit d Y).app ((stratumModulePull d f).obj M)).app
          (op n) := by
  obtain ⟨e, he⟩ := stratumScalarIso_exists d f n
  let b := proEtaleRingRestrictionPullbackInv f
    (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
    (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
    (d.projection_comm f n)
  have : IsIso b := proEtaleRingRestrictionPullbackInv_isIso f _ _ _ _ _ _ _ _ _
  refine ⟨asIso (b.app ((proEtaleRingExtension (d.projection X n)).obj M)) ≪≫
    (proEtaleRingRestrictScalars (d.projection Y n)).mapIso (e.app M), ?_⟩
  rw [stratumModuleUnit_component, stratumModuleUnit_component]
  exact he M

end

/-- The ordinary strict reduction comparison is uniquely fixed by its quotient unit.
Source: Stacks Tag 03EL; Bhatt--Scholze, Lemma 6.5.8(1)
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: finite constant coefficients pull back canonically, and the completed map
commutes with every quotient projection (proetale-constant-ring-map and four-corners).
The scalar-extension/pullback balancing map at level n sends a pulled-back tensor
x tensor q to the tensor of its pullbacks. These maps commute with quotient maps,
so they form an isomorphism of strict towers, natural in the input module. Their
composite with x maps to x tensor 1 is the target quotient unit. Conversely each
quotient unit is an epimorphism, because the completed projection is the quotient
by I^(n+1) (constant-completion-equivalence). Pullback is exact, so equality after
these epimorphisms determines every component, hence the natural isomorphism. -/
theorem stratumModuleReductionIso_exists :
    ∃! e : completedReductionModuleTowerFunctor X d ⋙ d.towerModulePull f ≅
        stratumModulePull d f ⋙ completedReductionModuleTowerFunctor Y d,
      ∀ M : reductionModules X (d.completedRing X),
        (d.towerModulePull f).map ((completedReductionModuleUnit d X).app M) ≫
            e.hom.app M =
          (d.constantPullbackIso f).hom.app M ≫
            (completedReductionModuleUnit d Y).app ((stratumModulePull d f).obj M) := by
  apply isoOfEpiAugmentations
    (d.constantTower X ⋙ d.towerModulePull f)
    (completedReductionModuleTowerFunctor X d ⋙ d.towerModulePull f)
    (stratumModulePull d f ⋙ completedReductionModuleTowerFunctor Y d)
    (Functor.whiskerRight (completedReductionModuleUnit d X) (d.towerModulePull f))
    ((d.constantPullbackIso f).hom ≫
      Functor.whiskerLeft (stratumModulePull d f) (completedReductionModuleUnit d Y))
  · intro M n
    let := stratumModuleUnit_epi d X M n.unop
    exact inferInstanceAs (Epi ((stratumModulePull d f).map
      (((completedReductionModuleUnit d X).app M).app n)))
  · intro M n
    obtain ⟨e, he⟩ := stratumModuleLevelIso d f n.unop M
    refine ⟨e, ?_⟩
    change (stratumModulePull d f).map
        (((completedReductionModuleUnit d X).app M).app n) ≫ e.hom =
      𝟙 _ ≫ ((completedReductionModuleUnit d Y).app ((stratumModulePull d f).obj M)).app n
    rw [Category.id_comp]
    exact he

/-- The ordinary comparison selected by its unique augmentation normalization.
Source: Stacks Tag 03EL (blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumModuleReductionIso := (stratumModuleReductionIso_exists d f).exists.choose

attribute [local instance] completedReductionModuleTowerFunctor_additive
attribute [local irreducible] HasDerivedCategory.standard
  cochainRepresentativeWhiskering complexCounitNat
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
  completedReductionTower CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors CategoryTheory.Functor.mapDerivedCategoryFactorsh
  CategoryTheory.Functor.mapDerivedCategoryNatIso

/-- The representative equation for the comparison of entire derived strict towers.
It uses actual universal counits and the ordinary strict comparison, so evaluations
alone do not specify a morphism in the derived category of towers.
Source: Stacks Tags 06YY, 03EL
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def StratumReductionFormula
    (e : completedReductionTower X d ⋙ d.towerPull f ≅
      d.pull f ⋙ completedReductionTower Y d) : Prop :=
  ∀ P : CochainComplex (reductionModules X (d.completedRing X)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing X) P →
      DerivedReductionComparisonFormula
        (stratumModulePull d f) (d.towerModulePull f)
        (completedReductionModuleTowerFunctor X d) (completedReductionModuleTowerFunctor Y d)
        (completedReductionTower X d) (completedReductionTower Y d)
        (completedReductionTowerComplexCounit X d) (completedReductionTowerComplexCounit Y d)
        (stratumModuleReductionIso d f) e P

private theorem stratumPull_flatKFlat
    (P : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
        (R := d.completedRing X) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing Y)
      (((stratumModulePull d f).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists f (d.completedRing X)
  rcases I with ⟨r, ra, rm, rz, ro, L, e, ea, ez, es⟩
  dsimp only at hI
  subst L
  let I : SheafOfModules.AlgebraicInverseImage
      (proEtaleSheafInverseImage f (Type (u + 1))) (d.completedRing X)
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.completedRing X)) :=
    ⟨r, ra, rm, rz, ro, proEtaleModuleInverseImage f (d.completedRing X), e, ea, ez, es⟩
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 X)).2.2.2.1
  have hobj (M) : (stratumModulePull d f).obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (d.integralRingIso f).hom (I.modules.obj M) := rfl
  have hmap : ∀ {M N} (g : M ⟶ N), (stratumModulePull d f).map g =
      eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (d.integralRingIso f).hom
          (I.modules.obj M) (I.modules.map g) ≫ eqToHom (hobj N).symm := by
    intro M N g
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  exact (SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1))) I (d.integralRingIso f).hom
    (stratumModulePull d f) hobj hmap P hP hflat).1

private noncomputable def stratumComplexCounit (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ completedReductionTower T d ⟶
      completedReductionComplexTowerFunctor T d ⋙ DerivedCategory.Q :=
  complexCounitNat (completedReductionModuleTowerFunctor T d)
    (completedReductionTower T d) (coherenceReductionTowerCounit T d)

private theorem stratumComplexCounit_app (T : Scheme.{u})
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
    (stratumComplexCounit d T).app P = completedReductionTowerComplexCounit T d P := by
  simpa only [stratumComplexCounit, completedReductionTowerComplexCounit] using
    complexCounitNat_app (completedReductionModuleTowerFunctor T d)
      (completedReductionTower T d) (coherenceReductionTowerCounit T d) P

attribute [local irreducible] stratumComplexCounit completedReductionModuleTowerFunctor
  completedReductionTowerComplexCounit reductionComplexCounit coherenceReductionTowerCounit

private theorem lift_normalized_iso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (ff : F.FullyFaithful)
    {X Y : C} {Z : D} (a : F.obj X ⟶ Z) (b : F.obj Y ⟶ Z)
    [IsIso a] [IsIso b] : ∃ e : X ≅ Y, F.map e.hom ≫ b = a := by
  refine ⟨ff.preimageIso (asIso a ≪≫ (asIso b).symm), ?_⟩
  change F.map (ff.preimage ((asIso a ≪≫ (asIso b).symm).hom)) ≫ b = a
  rw [ff.map_preimage]
  simp

private theorem natTrans_ext_of_good
    {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    (good : C → Prop)
    (res : ∀ X, ∃ (P : C) (p : P ⟶ X), good P ∧ IsIso (F.map p))
    (α β : F ⟶ G) (h : ∀ P, good P → α.app P = β.app P) : α = β := by
  ext X
  obtain ⟨P, p, hP, hp⟩ := res X
  let _ := hp
  apply (cancel_epi (F.map p)).1
  rw [α.naturality, β.naturality, h P hP]

private theorem comparisonOfCounits
    {B C D E : Type*} [Category B] [Category C] [Category D] [Category E]
    [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : B ⥤ C) (G : D ⥤ E) (RX : B ⥤ D) (RY : C ⥤ E)
    [F.Additive] [G.Additive] [RX.Additive] [RY.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (MY : DerivedCategory B ⥤ DerivedCategory D)
    (MX : DerivedCategory C ⥤ DerivedCategory E)
    (εX : DerivedCategory.Q ⋙ MY ⟶ RX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εY : DerivedCategory.Q ⋙ MX ⟶ RY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (cX : ∀ P : CochainComplex B ℤ, MY.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((RX.mapHomologicalComplex (.up ℤ)).obj P))
    (cY : ∀ P : CochainComplex C ℤ, MX.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((RY.mapHomologicalComplex (.up ℤ)).obj P))
    (hcX : ∀ P, εX.app P = cX P) (hcY : ∀ P, εY.app P = cY P)
    (e : RX ⋙ G ≅ F ⋙ RY) (good : ObjectProperty (CochainComplex B ℤ))
    (res : ∀ K, ∃ (L : CochainComplex B ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (hX : ∀ P, good P → IsIso (εX.app P))
    (hY : ∀ P, good P → IsIso (εY.app ((F.mapHomologicalComplex (.up ℤ)).obj P))) :
    ∃ τ : MY ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ MX,
      (∀ P, DerivedReductionComparisonFormula F G RX RY MY MX cX cY e τ P) ∧
      ∀ τ', (∀ P, good P → DerivedReductionComparisonFormula F G RX RY MY MX cX cY e τ' P) →
        τ' = τ := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let RXc := RX.mapHomologicalComplex (.up ℤ)
  let RYc := RY.mapHomologicalComplex (.up ℤ)
  let ord := NatIso.mapHomologicalComplex e (.up ℤ)
  let a : DerivedCategory.Q ⋙ (MY ⋙ G.mapDerivedCategory) ⟶
      Fc ⋙ RYc ⋙ DerivedCategory.Q :=
    Functor.whiskerRight εX G.mapDerivedCategory ≫
      Functor.whiskerLeft RXc G.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight ord.hom DerivedCategory.Q
  let b : DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ MX) ⟶
      Fc ⋙ RYc ⋙ DerivedCategory.Q :=
    Functor.whiskerRight F.mapDerivedCategoryFactors.hom MX ≫
      Functor.whiskerLeft Fc εY
  let ar := Functor.whiskerLeft good.ι a
  let br := Functor.whiskerLeft good.ι b
  have ha (P : good.FullSubcategory) : IsIso (ar.app P) := by
    let _ := hX P.obj P.property
    exact ((G.mapDerivedCategory.mapIso (asIso (εX.app P.obj))) ≪≫
      G.mapDerivedCategoryFactors.app (RXc.obj P.obj) ≪≫
        DerivedCategory.Q.mapIso (ord.app P.obj)).isIso_hom
  have hb (P : good.FullSubcategory) : IsIso (br.app P) := by
    let _ := hY P.obj P.property
    exact ((MX.mapIso (F.mapDerivedCategoryFactors.app P.obj)) ≪≫
      asIso (εY.app (Fc.obj P.obj))).isIso_hom
  have : IsIso ar := NatIso.isIso_of_isIso_app ar
  have : IsIso br := NatIso.isIso_of_isIso_app br
  let ff := cochainRepresentativeWhiskering good res (DerivedCategory E)
  clear_value ff
  obtain ⟨τ, heq⟩ := lift_normalized_iso
    ((Functor.whiskeringLeft _ _ (DerivedCategory E)).obj
      (good.ι ⋙ DerivedCategory.Q)) ff
    (X := MY ⋙ G.mapDerivedCategory) (Y := F.mapDerivedCategory ⋙ MX)
    (Z := good.ι ⋙ Fc ⋙ RYc ⋙ DerivedCategory.Q) ar br
  change Functor.whiskerLeft (good.ι ⋙ DerivedCategory.Q) τ.hom ≫ br = ar at heq
  have hrep : Functor.whiskerLeft DerivedCategory.Q τ.hom ≫ b = a := by
    apply natTrans_ext_of_good _ _ good ?_ _ _ ?_
    · intro P
      obtain ⟨L, p, hL, hp⟩ := res P
      have : IsIso (DerivedCategory.Q.map p) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
      refine ⟨L, p, hL, ?_⟩
      change IsIso (G.mapDerivedCategory.map (MY.map (DerivedCategory.Q.map p)))
      infer_instance
    · intro P hP
      exact NatTrans.congr_app heq ⟨P, hP⟩
  have hτ (P) : DerivedReductionComparisonFormula F G RX RY MY MX cX cY e τ P := by
    simpa only [DerivedReductionComparisonFormula, a, b, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, ord,
      NatIso.mapHomologicalComplex, hcX, hcY] using NatTrans.congr_app hrep P
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  apply Iso.ext
  apply ff.map_injective
  apply (cancel_mono br).1
  ext P
  change τ'.hom.app (DerivedCategory.Q.obj P.obj) ≫ b.app P.obj =
    τ.hom.app (DerivedCategory.Q.obj P.obj) ≫ b.app P.obj
  simpa only [DerivedReductionComparisonFormula, b, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, hcY] using
      (hτ' P.obj P.property).trans (hτ P.obj).symm

private theorem stratumComparison_from_counits :
    ∃ τ : completedReductionTower X d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower Y d,
      (∀ P, DerivedReductionComparisonFormula
        (stratumModulePull d f) (d.towerModulePull f)
        (completedReductionModuleTowerFunctor X d) (completedReductionModuleTowerFunctor Y d)
        (completedReductionTower X d) (completedReductionTower Y d)
        (completedReductionTowerComplexCounit X d) (completedReductionTowerComplexCounit Y d)
        (stratumModuleReductionIso d f) τ P) ∧
      ∀ τ', (∀ P : CochainComplex (reductionModules X (d.completedRing X)) ℤ,
        P.IsKFlatIndependentCoefficients ∧
          (∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
            (R := d.completedRing X) (P.X n)) →
        DerivedReductionComparisonFormula
          (stratumModulePull d f) (d.towerModulePull f)
          (completedReductionModuleTowerFunctor X d) (completedReductionModuleTowerFunctor Y d)
          (completedReductionTower X d) (completedReductionTower Y d)
          (completedReductionTowerComplexCounit X d) (completedReductionTowerComplexCounit Y d)
          (stratumModuleReductionIso d f) τ' P) → τ' = τ := by
  let good : ObjectProperty (CochainComplex (reductionModules X (d.completedRing X)) ℤ) :=
    fun P ↦ P.IsKFlatIndependentCoefficients ∧
      ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
        (R := d.completedRing X) (P.X n)
  have res (L : CochainComplex (reductionModules X (d.completedRing X)) ℤ) :
      ∃ P, ∃ p : P ⟶ L, good P ∧ QuasiIso p := by
    obtain ⟨P, p, hP, hflat, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := d.completedRing X) L
    exact ⟨P, p, ⟨hP, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (d.completedRing X) (P.X n)).symm
        (hflat n)⟩, hp⟩
  exact comparisonOfCounits
    (stratumModulePull d f) (d.towerModulePull f)
    (completedReductionModuleTowerFunctor X d) (completedReductionModuleTowerFunctor Y d)
    (completedReductionTower X d) (completedReductionTower Y d)
    (stratumComplexCounit d X) (stratumComplexCounit d Y)
    (completedReductionTowerComplexCounit X d) (completedReductionTowerComplexCounit Y d)
    (stratumComplexCounit_app d X) (stratumComplexCounit_app d Y)
    (stratumModuleReductionIso d f) good res
    (fun P hP ↦ by
      rw [stratumComplexCounit_app]
      exact towerCounit_isIso X d P hP.1)
    (fun P hP ↦ by
      rw [stratumComplexCounit_app]
      exact towerCounit_isIso Y d _ (stratumPull_flatKFlat d f P hP.1 hP.2))

private theorem unique_of_between {T : Sort*} (P Q R : T → Prop)
    (h : ∃ x, P x ∧ ∀ y, R y → y = x)
    (hPQ : ∀ x, P x → Q x) (hQR : ∀ x, Q x → R x) : ∃! x, Q x := by
  obtain ⟨x, hx, hu⟩ := h
  exact ⟨x, hPQ x hx, fun y hy ↦ hu y (hQR y hy)⟩

/-- The normalized strict tower comparison exists uniquely.
Source: Stacks Tags 06YS, 06YY, 03EL
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: use a K-flat resolution with flat terms (reduction-pullback-derived-tower).
Exact inverse image and identified-coefficient pullback carry it to a K-flat
representative. Apply the ordinary strict comparison, conjugated by the reduction
counits and exact-pullback localization factors, as in StratumReductionFormula.
Naturality and compatibility with quasi-isomorphisms descend this construction.
The inverse ordinary comparison descends to its inverse. Every derived object
has a K-flat representative, so the equation determines the comparison uniquely. -/
theorem stratumReductionIso_exists :
    ∃! e : completedReductionTower X d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower Y d,
      StratumReductionFormula d f e := by
  apply unique_of_between _ (StratumReductionFormula d f) _
    (stratumComparison_from_counits d f)
  · intro τ hτ P _
    exact hτ P
  · intro τ hτ P hP
    exact hτ P hP.1

/-- Canonical comparison of the actual strict quotient reduction towers.
Source: Stacks Tag 06YY (blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumReductionIso := (stratumReductionIso_exists d f).exists.choose

/-- The inverse-limit comparison is the mate of the canonical constant-tower
comparison under the two derived constant/limit adjunctions.
Source: Stacks Tag 0941 (blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumRlimComparison (T : DerivedCategory (d.towers X)) :
    (d.pull f).obj ((completedRlim X (d.completedRing X)).obj T) ⟶
      (completedRlim Y (d.completedRing Y)).obj ((d.towerPull f).obj T) :=
  (d.constantRlimAdjunction Y).unit.app
      ((d.pull f).obj ((completedRlim X (d.completedRing X)).obj T)) ≫
    (completedRlim Y (d.completedRing Y)).map
      ((d.derivedConstantPullbackIso f).inv.app ((completedRlim X (d.completedRing X)).obj T) ≫
        (d.towerPull f).map ((d.constantRlimAdjunction X).counit.app T))

/-- The canonical map between quotient completions, retaining its strict-tower map.
Source: Stacks Tags 0941 and 099M
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumCompletionComparison (K : d.derived X) :
    (d.pull f).obj ((completedRlim X (d.completedRing X)).obj
      ((completedReductionTower X d).obj K)) ⟶
    (completedRlim Y (d.completedRing Y)).obj
      ((completedReductionTower Y d).obj ((d.pull f).obj K)) :=
  stratumRlimComparison d f ((completedReductionTower X d).obj K) ≫
    (completedRlim Y (d.completedRing Y)).map ((stratumReductionIso d f).hom.app K)

/-- Termwise exact tower pullback commutes with evaluation by identity components.
Source: Stacks Tag 015F (blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumTowerEvaluationIso (n : ℕ) :
    d.towerPull f ⋙ reductionTowerDerivedEvaluation Y
        (reductionModuleRing Y (d.completedRing Y)) n ≅
      reductionTowerDerivedEvaluation X (reductionModuleRing X (d.completedRing X)) n ⋙
        d.pull f :=
  Functor.mapDerivedCategoryCompIso (d.towerModulePull f)
    (reductionTowerEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n) ≪≫
    Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (reductionTowerEvaluation X (reductionModuleRing X (d.completedRing X)) n)
      (stratumModulePull d f)).symm

section
attribute [local semireducible] completedReductionModuleTowerFunctor
  completedReductionCoefficient
attribute [local implicit_reducible] reductionChangeComplex completedReductionCoefficient
  reductionRestrict

private theorem stratumScalarComparison (n : ℕ)
    (e : proEtaleRingExtension (d.projection X n) ⋙
        proEtaleRingModulePullback f (d.finiteRing X n) (d.finiteRing Y n)
          (d.finiteRingIso f n) ≅
        stratumModulePull d f ⋙ proEtaleRingExtension (d.projection Y n))
    (he : ∀ M, (stratumModulePull d f).map
          ((pbcScalarAdjunction (d.projection X n)).unit.app M) ≫
        (proEtaleRingRestrictionPullbackInv f
          (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
          (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
          (d.projection_comm f n)).app ((proEtaleRingExtension (d.projection X n)).obj M) ≫
        (proEtaleRingRestrictScalars (d.projection Y n)).map (e.hom.app M) =
      (pbcScalarAdjunction (d.projection Y n)).unit.app ((stratumModulePull d f).obj M))
    (P : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ i, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := d.completedRing X) (P.X i)) :
    (d.chi f n).inv.app (DerivedCategory.Q.obj P) ≫
      (d.finitePull f n).map (reductionScalarComplexCounit X (d.projection X n) P) ≫
      (proEtaleRingModulePullback f (d.finiteRing X n) (d.finiteRing Y n)
        (d.finiteRingIso f n)).mapDerivedCategoryFactors.hom.app
          ((reductionChangeComplex X (d.projection X n)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
    (d.reduction Y n).map ((stratumModulePull d f).mapDerivedCategoryFactors.hom.app P) ≫
      reductionScalarComplexCounit Y (d.projection Y n)
        (((stratumModulePull d f).mapHomologicalComplex (.up ℤ)).obj P) := by
  let E := proEtaleRingExtension (d.projection X n)
  let E' := proEtaleRingExtension (d.projection Y n)
  let R := proEtaleRingRestrictScalars (d.projection X n)
  let R' := proEtaleRingRestrictScalars (d.projection Y n)
  let F := stratumModulePull d f
  let G := proEtaleRingModulePullback f (d.finiteRing X n) (d.finiteRing Y n)
    (d.finiteRingIso f n)
  let b := proEtaleRingRestrictionPullbackInv f
    (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
    (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
    (d.projection_comm f n)
  have : IsIso b := proEtaleRingRestrictionPullbackInv_isIso f _ _ _ _ _ _ _ _ _
  let ρ := asIso b
  let bd := proEtaleRingRestrictionDerivedPullback f
    (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
    (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
    (d.projection_comm f n)
  have hb : bd.inv = (Functor.mapDerivedCategorySquareIso ρ).hom := by
    change (Functor.mapDerivedCategorySquareIso ρ.symm).inv = _
    have hi : Functor.mapDerivedCategorySquareIso ρ.symm =
        (Functor.mapDerivedCategorySquareIso ρ).symm :=
      Iso.ext (Functor.square_symm_hom ρ)
    simpa only [Iso.symm_inv] using congrArg (fun e ↦ e.inv) hi
  have hm (K : d.derived X) :
      (pbcDerivedScalarAdjunction (d.projection Y n)).unit.app ((d.pull f).obj K) ≫
        R'.mapDerivedCategory.map ((d.chi f n).inv.app K) =
      (d.pull f).map ((pbcDerivedScalarAdjunction (d.projection X n)).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso ρ).hom.app ((d.reduction X n).obj K) := by
    rw [← hb]
    exact (unit_mateEquiv_symm (pbcDerivedScalarAdjunction (d.projection X n))
      (pbcDerivedScalarAdjunction (d.projection Y n))
      (TwoSquare.mk _ _ _ _ bd.inv) K).symm
  have hh := DerivedScalarMate.mate_computes_resolving E E' R R'
    (pbcScalarAdjunction (d.projection X n)) (pbcScalarAdjunction (d.projection Y n))
    (d.reduction X n) (d.reduction Y n)
    (pbcDerivedScalarAdjunction (d.projection X n))
    (pbcDerivedScalarAdjunction (d.projection Y n))
    (complexCounitNat E (d.reduction X n) (reductionDerivedCounit X (d.projection X n)))
    (complexCounitNat E' (d.reduction Y n) (reductionDerivedCounit Y (d.projection Y n)))
    F G ρ (Functor.mapDerivedCategorySquareIso ρ)
    (fun K ↦ Functor.exactSquare_fac ρ K) e (d.chi f n).inv hm P
    (by
      rw [complexCounitNat_app]
      with_unfolding_all
        exact (pbcDerivedScalarAdjunction_exists (d.projection X n)).exists.choose_spec P hP)
    (by
      rw [complexCounitNat_app]
      with_unfolding_all
        exact (pbcDerivedScalarAdjunction_exists (d.projection Y n)).exists.choose_spec _
          (stratumPull_flatKFlat d f P hP hflat)) he
  dsimp only [E, E', F, G, proEtaleRingExtension] at hh
  simp only [complexCounitNat_app] at hh
  with_unfolding_all exact hh
private theorem stratumScalarRestrictedComparison (n : ℕ)
    (e : proEtaleRingExtension (d.projection X n) ⋙
        proEtaleRingModulePullback f (d.finiteRing X n) (d.finiteRing Y n)
          (d.finiteRingIso f n) ≅
        stratumModulePull d f ⋙ proEtaleRingExtension (d.projection Y n))
    (he : ∀ M, (stratumModulePull d f).map
          ((pbcScalarAdjunction (d.projection X n)).unit.app M) ≫
        (proEtaleRingRestrictionPullbackInv f
          (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
          (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
          (d.projection_comm f n)).app ((proEtaleRingExtension (d.projection X n)).obj M) ≫
        (proEtaleRingRestrictScalars (d.projection Y n)).map (e.hom.app M) =
      (pbcScalarAdjunction (d.projection Y n)).unit.app ((stratumModulePull d f).obj M))
    (P : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ i, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := d.completedRing X) (P.X i)) :
    let F := stratumModulePull d f
    let R := proEtaleRingRestrictScalars (d.projection X n)
    let R' := proEtaleRingRestrictScalars (d.projection Y n)
    let EP := (reductionChangeComplex X (d.projection X n)).obj P
    let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
    let b := proEtaleRingRestrictionPullbackInv f
      (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
      (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
      (d.projection_comm f n)
    let bd := proEtaleRingRestrictionDerivedPullback f
      (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
      (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
      (d.projection_comm f n)
    bd.inv.app ((d.reduction X n).obj (DerivedCategory.Q.obj P)) ≫
      R'.mapDerivedCategory.map ((d.chi f n).hom.app (DerivedCategory.Q.obj P)) ≫
      R'.mapDerivedCategory.map ((d.reduction Y n).map
        (F.mapDerivedCategoryFactors.hom.app P)) ≫
      R'.mapDerivedCategory.map (reductionScalarComplexCounit Y (d.projection Y n) FP) ≫
      R'.mapDerivedCategoryFactors.hom.app ((reductionChangeComplex Y (d.projection Y n)).obj FP)
    = F.mapDerivedCategory.map
        (R.mapDerivedCategory.map (reductionScalarComplexCounit X (d.projection X n) P) ≫
          R.mapDerivedCategoryFactors.hom.app EP) ≫
      F.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj EP) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b (.up ℤ)).app EP) ≫
      DerivedCategory.Q.map ((R'.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) := by
  dsimp only
  let F := stratumModulePull d f
  let G := proEtaleRingModulePullback f (d.finiteRing X n) (d.finiteRing Y n)
    (d.finiteRingIso f n)
  let R := proEtaleRingRestrictScalars (d.projection X n)
  let R' := proEtaleRingRestrictScalars (d.projection Y n)
  let EP := (reductionChangeComplex X (d.projection X n)).obj P
  let b := proEtaleRingRestrictionPullbackInv f
    (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
    (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
    (d.projection_comm f n)
  let bd := proEtaleRingRestrictionDerivedPullback f
    (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
    (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
    (d.projection_comm f n)
  have : IsIso b := proEtaleRingRestrictionPullbackInv_isIso f _ _ _ _ _ _ _ _ _
  let ρ := asIso b
  have hb : bd.inv = (Functor.mapDerivedCategorySquareIso ρ).hom := by
    change (Functor.mapDerivedCategorySquareIso ρ.symm).inv = _
    have hi : Functor.mapDerivedCategorySquareIso ρ.symm =
        (Functor.mapDerivedCategorySquareIso ρ).symm :=
      Iso.ext (Functor.square_symm_hom ρ)
    simpa only [Iso.symm_inv] using congrArg (fun e ↦ e.inv) hi
  have hs := stratumScalarComparison d f n e he P hP hflat
  have hs' : (d.chi f n).hom.app (DerivedCategory.Q.obj P) ≫
        (d.reduction Y n).map (F.mapDerivedCategoryFactors.hom.app P) ≫
        reductionScalarComplexCounit Y (d.projection Y n)
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (reductionScalarComplexCounit X (d.projection X n) P) ≫
        G.mapDerivedCategoryFactors.hom.app EP ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
    apply (cancel_epi ((d.chi f n).inv.app (DerivedCategory.Q.obj P))).1
    simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using hs.symm
  have hfac := Functor.exactSquare_fac ρ EP
  rw [← hb] at hfac
  erw [← R'.mapDerivedCategory.map_comp_assoc, ← R'.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [hs']
  simp only [Functor.map_comp, Category.assoc]
  erw [R'.mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)]
  erw [← reassoc_of% (bd.inv.naturality (reductionScalarComplexCounit X (d.projection X n) P))]
  erw [reassoc_of% hfac]
  rfl
private theorem stratumOrdinaryEvaluation (n : ℕ)
    (e : proEtaleRingExtension (d.projection X n) ⋙
        proEtaleRingModulePullback f (d.finiteRing X n) (d.finiteRing Y n)
          (d.finiteRingIso f n) ≅
        stratumModulePull d f ⋙ proEtaleRingExtension (d.projection Y n))
    (he : ∀ M, (stratumModulePull d f).map
          ((pbcScalarAdjunction (d.projection X n)).unit.app M) ≫
        (proEtaleRingRestrictionPullbackInv f
          (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
          (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
          (d.projection_comm f n)).app ((proEtaleRingExtension (d.projection X n)).obj M) ≫
        (proEtaleRingRestrictScalars (d.projection Y n)).map (e.hom.app M) =
      (pbcScalarAdjunction (d.projection Y n)).unit.app ((stratumModulePull d f).obj M))
    (M : reductionModules X (d.completedRing X)) :
    ((stratumModuleReductionIso d f).hom.app M).app (op n) =
      (proEtaleRingRestrictionPullbackInv f
        (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
        (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
        (d.projection_comm f n)).app ((proEtaleRingExtension (d.projection X n)).obj M) ≫
      (proEtaleRingRestrictScalars (d.projection Y n)).map (e.hom.app M) := by
  let := stratumModuleUnit_epi d X M n
  apply (cancel_epi ((stratumModulePull d f).map
    (((completedReductionModuleUnit d X).app M).app (op n)))).1
  have hu := CategoryTheory.NatTrans.congr_app
    ((stratumModuleReductionIso_exists d f).exists.choose_spec M) (op n)
  change (stratumModulePull d f).map
      (((completedReductionModuleUnit d X).app M).app (op n)) ≫
        ((stratumModuleReductionIso d f).hom.app M).app (op n) =
    𝟙 _ ≫ ((completedReductionModuleUnit d Y).app ((stratumModulePull d f).obj M)).app
      (op n) at hu
  rw [Category.id_comp, stratumModuleUnit_component, stratumModuleUnit_component] at hu
  rw [stratumModuleUnit_component]
  exact hu.trans (he M).symm

/-- Evaluation of the normalized strict comparison on a flat-term K-flat representative.
Source: Stacks Tags 03EL, 06YY and 015F
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: use the representative equation of `stratumReductionIso` and the defining
counit equation of `completedReductionEvaluation`. On the representative, the
ordinary strict comparison is the inverse scalar-extension mate, whose finite
component is `(d.chi f n).hom`; the quotient transition and the scalar restriction
comparison are exactly the maps displayed below. The two counit-normalized paths
therefore agree by the tensor balancing calculation. This is the K-flat resolving
step of the full evaluation theorem, and has strictly fewer hypotheses in its
conclusion than the theorem for arbitrary derived objects.
-/
theorem stratumReduction_evaluation_on_KFlat
    (n : ℕ) (P : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ i, SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := d.completedRing X) (P.X i)) :
    (reductionTowerDerivedEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n).map
        ((stratumReductionIso d f).hom.app (DerivedCategory.Q.obj P)) ≫
        (completedReductionEvaluation Y d n).app ((d.pull f).obj (DerivedCategory.Q.obj P)) =
      (stratumTowerEvaluationIso d f n).hom.app ((completedReductionTower X d).obj
        (DerivedCategory.Q.obj P)) ≫
        (d.pull f).map ((completedReductionEvaluation X d n).app (DerivedCategory.Q.obj P)) ≫
        (proEtaleRingRestrictionDerivedPullback f
          (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
          (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
          (d.projection_comm f n)).inv.app ((d.reduction X n).obj (DerivedCategory.Q.obj P)) ≫
        (reductionDerivedRestrict Y (d.projection Y n)).map
          ((d.chi f n).hom.app (DerivedCategory.Q.obj P)) := by
  obtain ⟨e, he⟩ := stratumScalarIso_exists d f n
  let F := stratumModulePull d f
  let G := d.towerModulePull f
  let RX := proEtaleRingRestrictScalars (d.projection X n)
  let RY := proEtaleRingRestrictScalars (d.projection Y n)
  let EX := reductionTowerEvaluation X (reductionModuleRing X (d.completedRing X)) n
  let EY := reductionTowerEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let EP := (reductionChangeComplex X (d.projection X n)).obj P
  let TXP := (completedReductionComplexTowerFunctor X d).obj P
  let TYP := (completedReductionComplexTowerFunctor Y d).obj FP
  let cx := completedReductionTowerComplexCounit X d P
  let cy := completedReductionTowerComplexCounit Y d FP
  let sx := RX.mapDerivedCategory.map (reductionScalarComplexCounit X (d.projection X n) P) ≫
    RX.mapDerivedCategoryFactors.hom.app EP
  let sy := RY.mapDerivedCategory.map (reductionScalarComplexCounit Y (d.projection Y n) FP) ≫
    RY.mapDerivedCategoryFactors.hom.app ((reductionChangeComplex Y (d.projection Y n)).obj FP)
  let sf := F.mapDerivedCategoryFactors.hom.app P
  let oc := (NatIso.mapHomologicalComplex (stratumModuleReductionIso d f) (.up ℤ)).hom.app P
  let bc := (NatTrans.mapHomologicalComplex
    (proEtaleRingRestrictionPullbackInv f
      (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
      (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
      (d.projection_comm f n)) (.up ℤ)).app EP
  let ec := (RY.mapHomologicalComplex (.up ℤ)).map
    ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)
  have hoc : (EY.mapHomologicalComplex (.up ℤ)).map oc = bc ≫ ec := by
    apply HomologicalComplex.hom_ext
    intro i
    exact stratumOrdinaryEvaluation d f n e he (P.X i)
  have hFP := stratumPull_flatKFlat d f P hP hflat
  have hεy : IsIso (reductionScalarComplexCounit Y (d.projection Y n) FP) :=
    scalarCounit_isIso Y (d.projection Y n) FP hFP
  have hsy : IsIso sy := by dsimp only [sy]; infer_instance
  let ly := d.reduction Y n ⋙ RY.mapDerivedCategory
  have hx : (completedReductionEvaluation X d n).app (DerivedCategory.Q.obj P) ≫ sx =
      EX.mapDerivedCategory.map cx ≫ EX.mapDerivedCategoryFactors.hom.app TXP := by
    exact (completedReductionEvaluation_exists X d n).choose_spec.1.2 P hP
  have hy : (completedReductionEvaluation Y d n).app (DerivedCategory.Q.obj FP) ≫ sy =
      EY.mapDerivedCategory.map cy ≫ EY.mapDerivedCategoryFactors.hom.app TYP := by
    exact (completedReductionEvaluation_exists Y d n).choose_spec.1.2 FP hFP
  have hn := (completedReductionEvaluation Y d n).naturality sf
  have ht := (stratumReductionIso_exists d f).exists.choose_spec P hP
  change (stratumReductionIso d f).hom.app (DerivedCategory.Q.obj P) ≫
      (completedReductionTower Y d).map sf ≫ cy =
    G.mapDerivedCategory.map cx ≫ G.mapDerivedCategoryFactors.hom.app TXP ≫
      DerivedCategory.Q.map oc at ht
  have hs := stratumScalarRestrictedComparison d f n e he P hP hflat
  have heval := Functor.exactSquare_fac (R := G) (G := EY) (L := EX) (S := F)
    (Iso.refl (G ⋙ EY) : G ⋙ EY ≅ EX ⋙ F) TXP
  have heval' : (stratumTowerEvaluationIso d f n).hom.app (DerivedCategory.Q.obj TXP) ≫
      F.mapDerivedCategory.map (EX.mapDerivedCategoryFactors.hom.app TXP) ≫
      F.mapDerivedCategoryFactors.hom.app ((EX.mapHomologicalComplex (.up ℤ)).obj TXP) =
    EY.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app TXP) ≫
      EY.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj TXP) := by
    have hid : DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (Iso.refl (G ⋙ EY)).hom (.up ℤ)).app TXP) = 𝟙 _ := by
      with_unfolding_all exact DerivedCategory.Q.map_id _
    rw [hid] at heval
    erw [Category.comp_id] at heval
    with_unfolding_all exact heval
  apply (cancel_mono (ly.map sf ≫ sy)).1
  simp only [Category.assoc]
  have hl : (completedReductionEvaluation Y d n).app
        ((d.pull f).obj (DerivedCategory.Q.obj P)) ≫ ly.map sf ≫ sy =
      EY.mapDerivedCategory.map ((completedReductionTower Y d).map sf ≫ cy) ≫
        EY.mapDerivedCategoryFactors.hom.app TYP := by
    erw [← Category.assoc, ← hn, Category.assoc, hy, Functor.map_comp]
    simp only [Functor.comp_map, Category.assoc]
    with_unfolding_all rfl
  rw [hl]
  have hr :
      (proEtaleRingRestrictionDerivedPullback f
        (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
        (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
        (d.projection_comm f n)).inv.app ((d.reduction X n).obj (DerivedCategory.Q.obj P)) ≫
        RY.mapDerivedCategory.map ((d.chi f n).hom.app (DerivedCategory.Q.obj P)) ≫
          ly.map sf ≫ sy =
      F.mapDerivedCategory.map sx ≫
        F.mapDerivedCategoryFactors.hom.app ((RX.mapHomologicalComplex (.up ℤ)).obj EP) ≫
          DerivedCategory.Q.map bc ≫ DerivedCategory.Q.map ec := by
    simpa only [ly, sy, sx, Functor.comp_map, Functor.map_comp, Category.assoc] using hs
  erw [hr]
  rw [← Functor.map_comp_assoc, ht]
  simp only [Functor.map_comp, Category.assoc]
  erw [EY.mapDerivedCategoryFactors.hom.naturality oc]
  simp only [Functor.comp_map]
  rw [hoc, Functor.map_comp]
  rw [← Category.assoc _ (F.mapDerivedCategory.map sx), ← F.mapDerivedCategory.map_comp,
    hx, F.mapDerivedCategory.map_comp]
  have hc := (stratumTowerEvaluationIso d f n).hom.naturality cx
  dsimp only [Functor.comp_map] at hc
  simp only [Category.assoc]
  erw [← reassoc_of% hc]
  erw [reassoc_of% heval']
  rfl

end

/-- Evaluations of the strict comparison are the actual finite-coefficient comparisons.
Source: Stacks Tags 03EL, 06YY and 015F
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: use the representative formula of stratumReductionIso. Evaluation of the
ordinary strict comparison is the inverse scalar-extension mate of the canonical
restriction/pullback comparison: both maps agree after the quotient epimorphism.
The universal evaluation counits identify its derived map with chi. The exact
restriction/pullback isomorphism retains the quotient action. Localizing this
identity on K-flat representatives proves the displayed equation. -/
theorem stratumReduction_evaluation (n : ℕ) (K : d.derived X) :
    (reductionTowerDerivedEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n).map
        ((stratumReductionIso d f).hom.app K) ≫
        (completedReductionEvaluation Y d n).app ((d.pull f).obj K) =
      (stratumTowerEvaluationIso d f n).hom.app ((completedReductionTower X d).obj K) ≫
        (d.pull f).map ((completedReductionEvaluation X d n).app K) ≫
        (proEtaleRingRestrictionDerivedPullback f
          (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
          (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
          (d.projection_comm f n)).inv.app ((d.reduction X n).obj K) ≫
        (reductionDerivedRestrict Y (d.projection Y n)).map ((d.chi f n).hom.app K) := by
  let E := reductionTowerDerivedEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n
  let R := reductionDerivedRestrict Y (d.projection Y n)
  let c := proEtaleRingRestrictionDerivedPullback f
    (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
    (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
    (d.projection_comm f n)
  let α := Functor.whiskerRight (stratumReductionIso d f).hom E ≫
    Functor.whiskerLeft (d.pull f) (completedReductionEvaluation Y d n)
  let β := Functor.whiskerLeft (completedReductionTower X d)
      (stratumTowerEvaluationIso d f n).hom ≫
    Functor.whiskerRight (completedReductionEvaluation X d n) (d.pull f) ≫
    Functor.whiskerLeft (d.reduction X n) c.inv ≫
    Functor.whiskerRight (d.chi f n).hom R
  obtain ⟨P, p, hP, hflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := d.completedRing X) (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  let e : DerivedCategory.Q.obj P ≅ K := asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso K
  have hh : α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P) := by
    exact stratumReduction_evaluation_on_KFlat d f n P hP
      (fun i ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (d.completedRing X) (P.X i)).symm
        (hflat i))
  have h : α.app K = β.app K := by
    apply (cancel_epi ((completedReductionTower X d ⋙ d.towerPull f ⋙ E).map e.hom)).1
    erw [α.naturality, β.naturality, hh]
    rfl
  exact h

attribute [local irreducible] completedReductionTowerUnit completedReductionModuleUnit

/-- The strict comparison preserves the actual augmentation from the constant tower.
Source: Stacks Tags 03EL, 06YY
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: on a K-flat representative the ordinary comparison carries the tensor unit
x tensor 1 to its pullback tensor 1, by its defining augmentation equation.
The reduction counits and the exact constant-pullback factors give the same
identity in the derived tower category. This proves the equation for every K by
resolving-class localization, including its fixed source Delta(FK). -/
theorem stratumReduction_augmentation (K : d.derived X) :
    (d.towerPull f).map ((completedReductionAugmentation d X).app K) ≫
        (stratumReductionIso d f).hom.app K =
      (d.derivedConstantPullbackIso f).hom.app K ≫
        (completedReductionAugmentation d Y).app ((d.pull f).obj K) := by
  exact completedReduction_augmentationOfComparison d f (stratumModuleReductionIso d f)
    (stratumReductionIso d f) (stratumModuleReductionIso_exists d f).exists.choose_spec
    (stratumReductionIso_exists d f).exists.choose_spec (stratumPull_flatKFlat d f) K

/-- These module inverse images are exact and preserve small limits; coefficient
identification is by the canonical completed map with its fixed finite projections.
Source: Bhatt--Scholze, Lemma 6.5.8(1); Stacks Tags 09AA, 03DB, 0E8K
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: for an immersion use proetale-immersion-limit-preservation. For a weakly
etale restriction use weakly-etale-localization: evaluation on the slice computes
limits sectionwise (module-sheaves-limits-sectionwise), and ringed-site restriction
is exact. Transport along the canonical ring isomorphism preserves these properties.
For either composite, compose the inverse images and their canonical coefficient
identifications; quotient projection identities identify the resulting coefficient
map with d.integralRingIso. This proves all four cases without assuming Y Noetherian. -/
theorem stratumRestriction_limits (hf : IsAdicStratumRestriction f) :
    (stratumModulePull d f).Additive ∧
      PreservesFiniteLimits (stratumModulePull d f) ∧
      PreservesFiniteColimits (stratumModulePull d f) ∧
      PreservesLimitsOfSize.{u + 1, u + 1} (stratumModulePull d f) ∧
      (∀ n : ℕ, (d.integralRingIso f).hom ≫ d.projection Y n =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection X n) ≫
          (d.finiteRingIso f n).hom) := by
  have hset : PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage f (Type (u + 1))) := by
    rcases hf with hi | hw | ⟨Z, i, j, hi, hj, rfl⟩ | ⟨Z, j, i, hj, hi, rfl⟩
    · let := hi
      exact (proEtale_immersion_inverseImage_preservesLimits f).1
    · let := hw
      exact restriction_preservesLimits f
    · let := hi
      let := hj
      let := (proEtale_immersion_inverseImage_preservesLimits i).1
      let := restriction_preservesLimits j
      exact comp_setLimits j i
    · let := hi
      let := hj
      let := (proEtale_immersion_inverseImage_preservesLimits i).1
      let := restriction_preservesLimits j
      exact comp_setLimits i j
  let := hset
  let := forgetAbelian_preservesLimits X
  let := forgetAbelian_preservesLimits Y
  let V := sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let : ReflectsLimitsOfSize.{u + 1, u + 1} V := reflectsLimits_of_reflectsIsomorphisms
  obtain ⟨e⟩ := abelianUnderlying f
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⋙ V) :=
    preservesLimits_of_natIso e.symm
  let : PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) :=
    preservesLimits_of_reflects_of_preserves _ V
  let R := d.completedRing X
  let B := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let W := SheafOfModules.toSheaf.{u + 1} B
  let := forgetModule_preservesLimits (reductionModuleRing X R)
  let := forgetModule_preservesLimits B
  let : ReflectsLimitsOfSize.{u + 1, u + 1} W := reflectsLimits_of_reflectsIsomorphisms
  obtain ⟨q⟩ := (proEtale_moduleInverseImage_comparison f R).1
  let : PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleModuleInverseImage f R ⋙ W) :=
    preservesLimits_of_natIso q.symm
  let : PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleModuleInverseImage f R) :=
    preservesLimits_of_reflects_of_preserves _ W
  let := proEtaleRingExtension_preservesLimits f R (d.completedRing Y) (d.integralRingIso f)
  let E := proEtaleRingExtensionPresheaf f R (d.completedRing Y) (d.integralRingIso f) ⋙
    PresheafOfModules.sheafification (𝟙 (reductionModuleRing Y (d.completedRing Y)).obj)
  have : PreservesLimitsOfSize.{u + 1, u + 1} E :=
    proEtaleRingExtension_preservesLimits f R (d.completedRing Y) (d.integralRingIso f)
  have hmod : PreservesLimitsOfSize.{u + 1, u + 1} (stratumModulePull d f) := by
    change PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleModuleInverseImage f R ⋙ E)
    infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance, hmod, d.projection_comm f⟩

/-- The canonical mate commutes with total derived strict inverse limit for the
specified restrictions, including schemes Y which are not Noetherian.
Source: Stacks Tag 0941; Bhatt--Scholze, Lemma 6.5.8
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: stratumRestriction_limits gives exactness and preservation of countable
products. Countable products are exact in both pro-etale module categories by
proetale-countable-products-exact. Apply exact-product-functor-strict-limit to the
specified total right-derived limit. Its normalized Roos comparison uses the
canonical product map on both signed fiber coordinates. Its ordinary limit
projection equation, hence its derived constant/limit adjunction equation,
identifies it with stratumRlimComparison. Thus this particular mate is invertible. -/
theorem stratumRlimComparison_isIso (hf : IsAdicStratumRestriction f)
    (T : DerivedCategory (d.towers X)) : IsIso (stratumRlimComparison d f T) := by
  let F := stratumModulePull d f
  let : PreservesLimitsOfSize.{u + 1, u + 1} F :=
    (stratumRestriction_limits d f hf).2.2.2.1
  let : PreservesLimitsOfSize.{0, 0} F := preservesSmallestLimits_of_preservesLimits F
  have hc : (d.constantPullbackIso f).symm = Functor.compConstIso ℕᵒᵖ F := by
    ext M n
    rfl
  have he : (d.derivedConstantPullbackIso f).inv =
      (Functor.mapDerivedCategorySquareIso (Functor.compConstIso ℕᵒᵖ F)).hom := by
    rw [← hc]
    simp only [AdicCoefficientDatum.derivedConstantPullbackIso,
      Functor.mapDerivedCategorySquareIso, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rfl
  let α := (mateEquiv (d.constantRlimAdjunction X) (d.constantRlimAdjunction Y)
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (Functor.compConstIso ℕᵒᵖ F)).hom))
  have : IsIso α := by
    exact productPreservingDerivedLimitMate_isIso F (fun _ ↦ inferInstance)
  have hm : stratumRlimComparison d f T = α.app T := by
    simp only [α, stratumRlimComparison, mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
      Functor.comp_obj, Category.id_comp,
      Functor.comp_map, Functor.map_comp, he]
    erw [Category.comp_id]
  rw [hm]
  infer_instance

/-- Restriction identifies the quotient completion and its unit, including the map
from the restricted input. The isomorphism is the prescribed strict-limit mate
followed by the normalized reduction-tower comparison.
Source: Bhatt--Scholze, Lemma 6.5.8(1),(2); Stacks Tags 0941, 099M
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: stratumRlimComparison_isIso and the strict tower isomorphism make their
composite invertible. Its unit equation follows from stratumReduction_augmentation
and the triangle identities for the two constant/derived-limit adjunctions.
Equivalently the normalized Roos comparison sends ((x tensor 1)_n,0) to
((F(x) tensor 1)_n,0), by exact-product-functor-strict-limit. Thus the equation
involves the specified quotient units and their actual source, not just endpoints. -/
theorem stratumCompletionComparison_unit [IsLocallyNoetherian X] [CompactSpace X]
    (hf : IsAdicStratumRestriction f) (K : d.derived X) :
    IsIso (stratumCompletionComparison d f K) ∧
      (d.pull f).map (d.completionUnit X K) ≫ stratumCompletionComparison d f K =
        d.completionUnit Y ((d.pull f).obj K) := by
  have hlim := stratumRlimComparison_isIso d f hf ((completedReductionTower X d).obj K)
  constructor
  · unfold stratumCompletionComparison
    infer_instance
  · let F := d.pull f
    let G := d.towerPull f
    let R := completedRlim Y (d.completedRing Y)
    let E := d.derivedConstantPullbackIso f
    let η := (d.constantRlimAdjunction Y).unit
    let u := (d.constantRlimAdjunction X).unit.app K
    let a := (completedReductionAugmentation d X).app K
    let T := (completedReductionTower X d).obj K
    let v := (d.constantRlimAdjunction X).counit.app T
    have ht : (d.derivedConstantTower X).map (u ≫
        (completedRlim X (d.completedRing X)).map a) ≫ v = a := by
      simp only [Functor.map_comp, Category.assoc]
      change (d.derivedConstantTower X).map u ≫
        (d.derivedConstantTower X).map ((completedRlim X (d.completedRing X)).map a) ≫
          (d.constantRlimAdjunction X).counit.app T = a
      rw [(d.constantRlimAdjunction X).counit_naturality a]
      simp [u]
    have he := E.inv.naturality (u ≫
      (completedRlim X (d.completedRing X)).map a)
    dsimp only [Functor.comp_map] at he
    have hn := η.naturality (F.map (u ≫
      (completedRlim X (d.completedRing X)).map a))
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    change F.map (u ≫ (completedRlim X (d.completedRing X)).map a) ≫
      (η.app (F.obj ((completedRlim X (d.completedRing X)).obj T)) ≫
        R.map (E.inv.app ((completedRlim X (d.completedRing X)).obj T) ≫ G.map v)) ≫
          R.map ((stratumReductionIso d f).hom.app K) = _
    rw [Category.assoc, ← Category.assoc _ (η.app _) _, hn]
    change (η.app (F.obj K) ≫ R.map
      ((d.derivedConstantTower Y).map (F.map (u ≫
        (completedRlim X (d.completedRing X)).map a)))) ≫
      R.map (E.inv.app ((completedRlim X (d.completedRing X)).obj T) ≫ G.map v) ≫
        R.map ((stratumReductionIso d f).hom.app K) = _
    have hb : (d.derivedConstantTower Y).map (F.map (u ≫
        (completedRlim X (d.completedRing X)).map a)) ≫
          (E.inv.app ((completedRlim X (d.completedRing X)).obj T) ≫ G.map v) ≫
            (stratumReductionIso d f).hom.app K =
        (completedReductionAugmentation d Y).app (F.obj K) := by
      simp only [← Category.assoc]
      rw [he]
      simp only [Category.assoc]
      change E.inv.app K ≫
        G.map ((d.derivedConstantTower X).map (u ≫
          (completedRlim X (d.completedRing X)).map a)) ≫
            G.map v ≫ (stratumReductionIso d f).hom.app K = _
      rw [← G.map_comp_assoc, ht, stratumReduction_augmentation d f K]
      exact Iso.inv_hom_id_app_assoc E K _
    rw [Category.assoc, ← R.map_comp, ← R.map_comp, hb]
    rfl

/-- Intrinsic completeness is preserved, with arbitrary representative realizations.
Source: Bhatt--Scholze, Lemma 6.5.8; Stacks Tags 099M, 0A0E
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: the constant-completion equivalence, via the published unit-normalized
Koszul/quotient comparison, identifies invertibility of each intrinsic unit with
invertibility of its quotient completion unit. stratumCompletionComparison_unit
identifies the restricted quotient unit with the target unit. A functor preserves
invertibility, so an invertible source intrinsic unit gives an invertible target
intrinsic unit. The comparison applies to every supplied representative on Y. -/
theorem stratumIntrinsicComplete_preserved [IsLocallyNoetherian X] [CompactSpace X]
    (hf : IsAdicStratumRestriction f)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived X)
    (C : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (D : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ)
    (eD : DerivedCategory.Q.obj D ≅ (d.pull f).obj K) :
    IsDerivedCompleteIntrinsic X d r a ha K C eC →
      IsDerivedCompleteIntrinsic Y d r a ha ((d.pull f).obj K) D eD := by
  intro hK
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d r a ha K C eC
  obtain ⟨e, he⟩ := completedKoszulQuotientComparison Y d r a ha
    ((d.pull f).obj K) D eD
  change intrinsicCompletionUnit X d r a ha K C eC ≫ c.hom = d.completionUnit X K at hc
  change intrinsicCompletionUnit Y d r a ha ((d.pull f).obj K) D eD ≫ e.hom =
    d.completionUnit Y ((d.pull f).obj K) at he
  have : IsIso (d.completionUnit X K) := by
    rw [← hc]
    let : IsIso (intrinsicCompletionUnit X d r a ha K C eC) := hK
    infer_instance
  obtain ⟨hcomp, hu⟩ := stratumCompletionComparison_unit d f hf K
  have : IsIso (d.completionUnit Y ((d.pull f).obj K)) := by
    rw [← hu]
    infer_instance
  change IsIso (intrinsicCompletionUnit Y d r a ha ((d.pull f).obj K) D eD)
  exact (isIso_comp_right_iff _ e.hom).mp (he ▸ inferInstance)

private def stratumPullUnderlying :
    SheafOfModules.toSheaf (reductionModuleRing X (d.completedRing X)) ⋙
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ≅
      stratumModulePull d f ⋙
        SheafOfModules.toSheaf (reductionModuleRing Y (d.completedRing Y)) := by
  let adj := proEtaleRingModuleAdjunction f (d.completedRing X) (d.completedRing Y)
    (d.integralRingIso f)
  let ab := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  let U := SheafOfModules.toSheaf (reductionModuleRing X (d.completedRing X))
  let V := SheafOfModules.toSheaf (reductionModuleRing Y (d.completedRing Y))
  let e (M : reductionModules X (d.completedRing X)) :=
    (ab.homEquiv _ _).symm (U.map (adj.unit.app M))
  have he (M) : IsIso (e M) := ringUnitComparison f _ _ _ adj M
  refine NatIso.ofComponents (fun M ↦ asIso (e M)) ?_
  intro M N h
  apply (ab.homEquiv _ _).injective
  change ab.homEquiv _ _
      ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map (U.map h) ≫ e N) =
    ab.homEquiv _ _ (e M ≫ V.map ((stratumModulePull d f).map h))
  rw [ab.homEquiv_naturality_left, ab.homEquiv_naturality_right]
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at *
  simp only [e, Functor.id_obj, Equiv.apply_symm_apply]
  have hn := congrArg U.map (adj.unit.naturality h)
  have hn' : U.map h ≫ U.map (adj.unit.app N) =
      U.map (adj.unit.app M) ≫ U.map
        ((proEtaleRingModuleDirectImage f (d.completedRing X) (d.completedRing Y)
          (d.integralRingIso f)).map ((stratumModulePull d f).map h)) := by
    simpa only [Functor.map_comp, Functor.id_map, Functor.comp_map] using hn
  rw [hn']
  congr 1

private theorem stratumPull_detects (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (S : FiniteLocallyClosedStratification X)
    (V : ∀ i : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain i))
    {K L : d.derived X} (g : K ⟶ L)
    (hg : ∀ (i : Fin S.n) (j : (V i).I₀),
      IsIso ((d.pull ((V i).f j ≫ S.immersion i)).map g)) : IsIso g := by
  have : IsNoetherian X := {}
  let S' := Stratification.ofNoetherianSpace S.n S.stratum S.isLocallyClosed_stratum
    S.iUnion_stratum_eq_univ S.pairwise_disjoint_stratum
    S.domain S.immersion S.isImmersion S.range_immersion
  have hm (M : reductionModules X (d.completedRing X))
      (hM : ∀ (i : Fin S.n) (j : (V i).I₀),
        IsZero ((stratumModulePull d ((V i).f j ≫ S.immersion i)).obj M)) : IsZero M := by
    have hz : IsZero ((SheafOfModules.toSheaf _).obj M) := by
      apply proEtale_isZero_of_stratum_cover X S' V
      intro i j
      exact ((SheafOfModules.toSheaf _).map_isZero (hM i j)).of_iso
        ((stratumPullUnderlying d ((V i).f j ≫ S.immersion i)).app M)
    apply (IsZero.iff_id_eq_zero M).2
    apply (SheafOfModules.toSheaf _).map_injective
    simpa using hz.eq_of_src ((SheafOfModules.toSheaf _).map (𝟙 M))
      ((SheafOfModules.toSheaf _).map (0 : M ⟶ M))
  have hz (M : d.derived X)
      (hM : ∀ (i : Fin S.n) (j : (V i).I₀),
        IsZero ((d.pull ((V i).f j ≫ S.immersion i)).obj M)) : IsZero M := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro q
    apply hm
    intro i j
    let P := stratumModulePull d ((V i).f j ≫ S.immersion i)
    exact ((DerivedCategory.homologyFunctor _ q).map_isZero (hM i j)).of_iso
      ((P.mapDerivedCategoryHomologyFunctorIso q).app M)
  obtain ⟨M, a, b, hT⟩ := Pretriangulated.distinguished_cocone_triangle g
  apply (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1
  apply hz
  intro i j
  let P := d.pull ((V i).f j ≫ S.immersion i)
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (P.map_distinguished _ hT)).2 (hg i j)

/-- Intrinsic completeness is detected by every chosen pro-etale cover of every
stratum of a finite locally closed stratification.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication; Stacks Tags 09AH, 09AB
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: preservation proves the forward direction for every stratum/cover composite.
Conversely the unit-normalized Koszul/quotient comparison makes every local quotient
unit invertible. stratumCompletionComparison_unit identifies these maps with the
restrictions of the single global quotient unit. Noetherian-stratum-detection,
applied to the completed ring, reflects its invertibility. On a Noetherian scheme
locally closed strata are constructible, so the recorded finite locally closed
stratification supplies exactly that detection theorem's stratification. Finally
compare the global quotient unit with the supplied intrinsic unit. This uses no
boundedness and no Noetherian hypothesis on the covering members. -/
theorem stratum_completion_unit_restriction (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X]
    (S : FiniteLocallyClosedStratification X)
    (V : ∀ i : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain i))
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived X)
    (C : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K) :
    IsDerivedCompleteIntrinsic X d r a ha K C eC ↔
      ∀ (i : Fin S.n) (j : (V i).I₀),
        ∀ (D : CochainComplex
          (reductionModules ((V i).X j) (d.completedRing ((V i).X j))) ℤ)
          (eD : DerivedCategory.Q.obj D ≅ (d.pull ((V i).f j ≫ S.immersion i)).obj K),
          IsDerivedCompleteIntrinsic ((V i).X j) d r a ha
            ((d.pull ((V i).f j ≫ S.immersion i)).obj K) D eD := by
  have hf (i : Fin S.n) (j : (V i).I₀) :
      IsAdicStratumRestriction ((V i).f j ≫ S.immersion i) := by
    refine Or.inr (Or.inr (Or.inl ⟨S.domain i, S.immersion i, (V i).f j,
      S.isImmersion i, ?_, rfl⟩))
    exact ((ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 (V i).mem₀.2).2 j
  constructor
  · intro h i j D eD
    exact stratumIntrinsicComplete_preserved d _ (hf i j) r a ha K C eC D eD h
  · intro h
    obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d r a ha K C eC
    change intrinsicCompletionUnit X d r a ha K C eC ≫ c.hom = d.completionUnit X K at hc
    have hu : IsIso (d.completionUnit X K) := by
      apply stratumPull_detects d X S V
      intro i j
      let f := (V i).f j ≫ S.immersion i
      let M := (d.pull f).obj K
      let D := DerivedCategory.Q.objPreimage M
      let eD := DerivedCategory.Q.objObjPreimageIso M
      have hM := h i j D eD
      obtain ⟨e, he⟩ := completedKoszulQuotientComparison _ d r a ha M D eD
      change intrinsicCompletionUnit _ d r a ha M D eD ≫ e.hom = d.completionUnit _ M at he
      have : IsIso (d.completionUnit _ M) := by
        rw [← he]
        let : IsIso (intrinsicCompletionUnit _ d r a ha M D eD) := hM
        infer_instance
      obtain ⟨hi, hiu⟩ := stratumCompletionComparison_unit d f (hf i j) K
      have : IsIso ((d.pull f).map (d.completionUnit X K) ≫
          stratumCompletionComparison d f K) := hiu ▸ inferInstance
      exact (isIso_comp_right_iff _ (stratumCompletionComparison d f K)).mp this
    change IsIso (intrinsicCompletionUnit X d r a ha K C eC)
    exact (isIso_comp_right_iff _ c.hom).mp (hc ▸ hu)

end AlgebraicGeometry.Scheme
