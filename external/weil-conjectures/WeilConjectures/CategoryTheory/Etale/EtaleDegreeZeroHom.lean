/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.CategoryTheory.Adjunction.Limits
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
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.HomCongr

/-! # Local derived morphisms between degree-zero objects

Source: Stacks Project, Tags 05RU and 03EH.
(blueprint: lem-amb-etale-degree-zero-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Transport Hom sets to the image of a fully faithful functor using specified
object isomorphisms. The inverse image is uniquely determined by full faithfulness. -/
@[irreducible]
def fullyFaithfulHomEquivOfIsos
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D) (hT : T.FullyFaithful)
    {K L : D} {M N : C} (α : K ≅ T.obj M) (β : L ≅ T.obj N) :
    (K ⟶ L) ≃ (M ⟶ N) :=
  (Iso.homCongr α β).trans hT.homEquiv.symm

/-- The inverse of the transported Hom correspondence is conjugated functorial image. -/
theorem fullyFaithfulHomEquivOfIsos_symm_apply
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D) (hT : T.FullyFaithful)
    {K L : D} {M N : C} (α : K ≅ T.obj M) (β : L ≅ T.obj N) (a : M ⟶ N) :
    (fullyFaithfulHomEquivOfIsos T hT α β).symm a = α.hom ≫ T.map a ≫ β.inv := by
  unfold fullyFaithfulHomEquivOfIsos
  rfl

/-- Full faithfulness after a specified comparison of two composites. -/
@[irreducible]
def fullyFaithfulHomEquivOfCompIso
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (S : C ⥤ D) (S' : C' ⥤ D') (hS' : S'.FullyFaithful)
    (G : D ⥤ D') (R : C ⥤ C') (η : S ⋙ G ≅ R ⋙ S')
    {K : D} {M N : C} (α : K ≅ S.obj M) :
    (G.obj K ⟶ G.obj (S.obj N)) ≃ (R.obj M ⟶ R.obj N) :=
  fullyFaithfulHomEquivOfIsos S' hS' (G.mapIso α ≪≫ η.app M) (η.app N)

/-- Naturality identifies the inverse correspondence on global maps. -/
theorem fullyFaithfulHomEquivOfCompIso_map
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (S : C ⥤ D) (S' : C' ⥤ D') (hS' : S'.FullyFaithful)
    (G : D ⥤ D') (R : C ⥤ C') (η : S ⋙ G ≅ R ⋙ S')
    {K : D} {M N : C} (α : K ≅ S.obj M) (a : M ⟶ N) :
    fullyFaithfulHomEquivOfCompIso S S' hS' G R η α (G.map (α.hom ≫ S.map a)) =
      R.map a := by
  apply (fullyFaithfulHomEquivOfCompIso S S' hS' G R η α).symm.injective
  rw [Equiv.symm_apply_apply]
  simp only [fullyFaithfulHomEquivOfCompIso, fullyFaithfulHomEquivOfIsos_symm_apply]
  have hn := η.hom.naturality a
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Category.assoc]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, Category.comp_id]

/-- An injective Hom correspondence detects an equation after an isomorphism. -/
theorem homEquiv_comp_iso_eq_iff
    {D : Type*} [Category D] {K L P : D} {T : Type*}
    (e : (K ⟶ L) ≃ T) (m : K ⟶ L) (a : T) (he : e m = a)
    (β : L ≅ P) (τ : K ⟶ P) :
    m ≫ β.hom = τ ↔ a = e (τ ≫ β.inv) := by
  constructor
  · intro h
    have hm : m = τ ≫ β.inv := by
      rw [← h, Category.assoc, β.hom_inv_id, Category.comp_id]
    rw [← he, hm]
  · intro h
    have hm : m = τ ≫ β.inv := e.injective (he.trans h)
    rw [hm, Category.assoc, β.inv_hom_id, Category.comp_id]

end CategoryTheory

namespace DerivedCategory

/-- The full-faithfulness data of the standard single-degree embedding. The preimage
is uniquely specified by that functor, so this packages its existing canonical API. -/
@[irreducible]
def fullyFaithfulSingleFunctor {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) : (singleFunctor C n).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

end DerivedCategory

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftDerivedFunctor upperStar
  _root_.DerivedCategory.singleFunctors ordinaryFinitePullback

/-- Inverse image of a single complex is the single complex of its restriction.
Source: Stacks Project, Tags 05RU and 03EH.
(blueprint: lem-amb-etale-degree-zero-hom). -/
@[irreducible]
def etaleSingleRestrictionIso (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] :
    _root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat A)) 0 ⋙
        ordinaryFinitePullback A f ≅
      localizationRestriction (ModuleCat.{u + 1} A) f inferInstance ⋙
        _root_.DerivedCategory.singleFunctor _ 0 :=
  by
    unfold ordinaryFinitePullback
    exact singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f ≪≫
      Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
        f inferInstance) (_root_.DerivedCategory.singleFunctor
          (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)

/-- A local derived morphism corresponds to a sheaf morphism by degree-zero full
faithfulness. Source: Stacks Project, Tags 05RU and 03EH.
(blueprint: lem-amb-etale-degree-zero-hom). -/
@[irreducible]
def etaleDegreeZeroHomEquiv (A : Type (u + 1)) [CommRing A]
    {X U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {K : DerivedCategoryModule A X}
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M) :=
  fullyFaithfulHomEquivOfCompIso
    (_root_.DerivedCategory.singleFunctor _ 0)
    (_root_.DerivedCategory.singleFunctor _ 0)
    (_root_.DerivedCategory.fullyFaithfulSingleFunctor 0)
    (ordinaryFinitePullback A f)
    (localizationRestriction (ModuleCat.{u + 1} A) f inferInstance)
    (etaleSingleRestrictionIso A f) (N := N) α

/-- Naturality of the degree-zero Hom correspondence on global maps.
Source: Stacks Project, Tags 05RU and 03EH.
(blueprint: lem-amb-etale-degree-zero-hom). -/
theorem etaleDegreeZeroHomEquiv_map (A : Type (u + 1)) [CommRing A]
    {X U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {K : DerivedCategoryModule A X}
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M) (a : M ⟶ N) :
    etaleDegreeZeroHomEquiv A f α
        ((ordinaryFinitePullback A f).map
          (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map a)) =
      (localizationRestriction (ModuleCat.{u + 1} A) f inferInstance).map a := by
  unfold etaleDegreeZeroHomEquiv
  exact fullyFaithfulHomEquivOfCompIso_map _ _ _ _ _ _ α a

/-- The degree-zero correspondence converts the constant-object normalization
into the restriction equation for the corresponding sheaf map.
Source: Stacks Project, Tags 05RU and 03EH.
(blueprint: lem-amb-etale-degree-zero-hom). -/
theorem etaleDegreeZeroHomEquiv_unit_normalization
    (A : Type (u + 1)) [CommRing A] {X U : Scheme.{u}} (f : U ⟶ X) [Etale f]
    {K : DerivedCategoryModule A X}
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M)
    (a : M ⟶ ordinaryFiniteConstant A X)
    (τ : (ordinaryFinitePullback A f).obj K ⟶ ordinaryFiniteUnit A U) :
    (ordinaryFinitePullback A f).map
        (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map a) ≫
          (ordinaryFiniteUnitPullback A f).hom = τ ↔
      (localizationRestriction (ModuleCat.{u + 1} A) f inferInstance).map a =
        etaleDegreeZeroHomEquiv A f α (τ ≫ (ordinaryFiniteUnitPullback A f).inv) := by
  exact homEquiv_comp_iso_eq_iff
    (etaleDegreeZeroHomEquiv A f (N := ordinaryFiniteConstant A X) α)
    ((ordinaryFinitePullback A f).map
      (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map a))
    ((localizationRestriction (ModuleCat.{u + 1} A) f inferInstance).map a)
    (etaleDegreeZeroHomEquiv_map A f α a) (ordinaryFiniteUnitPullback A f) τ

end AlgebraicGeometry.Etale
