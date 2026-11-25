/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! The right conjugate of the prescribed scalar associator.

## References

* Stacks Tags 06YY, 07A6 and 0D6D
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Limits CategoryTheory.Functor
open SheafOfModules.SuccessiveDerivedQuotient

private local instance proEtSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local irreducible] completedAdicChange completedAdicDerivedChange
attribute [local irreducible] reductionChange reductionDerivedChange
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] SheafOfModules.monoidalCategory

private noncomputable def publishedPresentation (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    Presentation.{u + 1, u, u + 1, u + 2} a where
  ordinary := reductionChange T a
  obj_eq := reductionChange_obj_eq T a
  map_eq := reductionChange_map_eq T a
  additive := reductionChangeAdditive T a
  derived := reductionDerivedChange T a
  counit := reductionDerivedCounit T a
  universal := reductionDerivedUniversal T a

private theorem complexCounitApp
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] (L : DerivedCategory D ⥤ DerivedCategory E)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex D ℤ) :
    reductionComplexCounit F L ε P = ε.app ((HomotopyCategory.quotient _ _).obj P) := by
  dsimp only [reductionComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors]
  erw [L.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  exact Category.comp_id _

private theorem quotientMap
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    {P Q : CochainComplex D ℤ} (f : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) =
      DerivedCategory.Q.map f := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality f
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom] at h
  erw [Category.comp_id, Category.id_comp] at h
  exact h

private theorem homComparisonUnit
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) (G : E ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (L : DerivedCategory D ⥤ DerivedCategory E)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (d : L ⊣ G.mapDerivedCategory)
    (h : ∀ (H : HomotopyCategory D (.up ℤ))
      (K : HomotopyCategory E (.up ℤ))
      (f : (F.mapHomotopyCategory (.up ℤ)).obj H ⟶ K),
      d.homEquiv _ _ (ε.app H ≫ DerivedCategory.Qh.map f) =
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).homEquiv H K f) ≫
          G.mapDerivedCategoryFactorsh.inv.app K)
    (P : CochainComplex D ℤ) :
    d.unit.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (reductionComplexCounit F L ε P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P) := by
  have hp := h ((HomotopyCategory.quotient _ _).obj P)
    ((F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) (𝟙 _)
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hp
  simp only [Adjunction.homEquiv_unit] at hp
  erw [(G.mapHomotopyCategory (.up ℤ)).map_id, Category.comp_id] at hp
  have hp' := congrArg (fun f ↦ f ≫ G.mapDerivedCategoryFactorsh.hom.app _) hp
  simp only [Category.assoc, Iso.inv_hom_id_app] at hp'
  erw [Category.comp_id] at hp'
  change d.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
    G.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
    G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
      ((HomotopyCategory.quotient _ _).obj P)) at hp'
  erw [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hp'
  dsimp only [reductionComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at hp' ⊢
  erw [L.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  erw [G.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id, Category.comp_id,
    Category.comp_id] at hp'
  erw [Category.comp_id]
  erw [Category.id_comp] at hp'
  erw [quotientMap] at hp'
  exact hp'

private theorem publishedTensor (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : reductionModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    sectionTensor (publishedPresentation T a) M U s x = pbcTensorSection a M U s x := by
  dsimp only [sectionTensor, SheafOfModules.SuccessiveDerivedQuotient.pure,
    publishedPresentation, pbcTensorSection,
    completedAdicChangeTensor, completedAdicChange]
  with_unfolding_all rfl

private theorem publishedAdjData (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (d : AdjData.{u + 1, u, u + 1, u + 2} (publishedPresentation T a)) :
    d.ordinary = pbcScalarAdjunction a ∧ d.derived = pbcDerivedScalarAdjunction a := by
  have ho : d.ordinary = pbcScalarAdjunction a := by
    apply (pbcScalarAdjunction_exists a).unique
    · intro M V x
      exact (d.ordinary_unit M V x).trans (publishedTensor T a M V 1 x)
    · exact (pbcScalarAdjunction_exists a).exists.choose_spec
  refine ⟨ho, ?_⟩
  apply (pbcDerivedScalarAdjunction_exists a).unique
  · intro P hp
    have h := homComparisonUnit (pbcExtend a) (pbcRestrict a)
      d.ordinary (pbcDerivedExtend a) (pbcExtensionCounit a)
      d.derived d.hom_comparison P
    rw [ho] at h
    exact h
  · exact (pbcDerivedScalarAdjunction_exists a).exists.choose_spec

private noncomputable def publishedData (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    AdjData.{u + 1, u, u + 1, u + 2} (publishedPresentation T a) :=
  Classical.choice (adjData_exists (publishedPresentation T a))

private theorem publishedComp_exists (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    ∃! e : reductionDerivedChange T a ⋙ reductionDerivedChange T b ≅
        reductionDerivedChange T c,
      e = derivedComp (publishedPresentation T) (publishedData T) a b ≪≫
        eqToIso (congrArg (fun f ↦ reductionDerivedChange T f) h) := by
  exact ⟨_, rfl, fun _ he ↦ he⟩

-- Keep the comparison behind its proved equation: projecting a concrete composite
-- adjunction otherwise unfolds the complete chosen localization during kernel checking.
private noncomputable def publishedComp (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    reductionDerivedChange T a ⋙ reductionDerivedChange T b ≅
      reductionDerivedChange T c :=
  (publishedComp_exists T a b c h).exists.choose

private theorem publishedComp_eq (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c) :
    publishedComp T a b c h =
      derivedComp (publishedPresentation T) (publishedData T) a b ≪≫
        eqToIso (congrArg (fun f ↦ reductionDerivedChange T f) h) :=
  (publishedComp_exists T a b c h).exists.choose_spec

private theorem publishedRepresentative (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) (c : R ⟶ V) (h : a ≫ b = c)
    (P : CochainComplex (reductionModules T R) ℤ) :
    (publishedComp T a b c h).hom.app
        (DerivedCategory.Q.obj P) ≫ reductionScalarComplexCounit T c P =
      (reductionDerivedChange T b).map (reductionScalarComplexCounit T a P) ≫
        reductionScalarComplexCounit T b ((reductionChangeComplex T a).obj P) ≫
        DerivedCategory.Q.map (reductionBalance T a b c h P) := by
  rw [publishedComp_eq]
  subst c
  let e := ordinaryComp (publishedPresentation T)
    (fun a ↦ (publishedData T a).ordinary) a b
  have he : (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P =
      reductionBalance T a b (a ≫ b) rfl P := by
    apply (reductionBalance_exists T a b (a ≫ b) rfl P).unique
    · refine ⟨by infer_instance, ?_⟩
      intro n U s r x
      have hh := ordinaryComp_hom (publishedPresentation T)
        (fun a ↦ (publishedData T a).ordinary)
        (fun a ↦ (publishedData T a).ordinary_unit) a b (P.X n) U x r s
      rw [mul_comm] at hh
      simp only [publishedTensor] at hh
      dsimp only [reductionTensorSection]
      with_unfolding_all exact hh
    · exact (reductionBalance_exists T a b (a ≫ b) rfl P).exists.choose_spec
  have hd := derivedComp_representative (publishedPresentation T) (publishedData T)
    a b ((HomotopyCategory.quotient _ _).obj P)
  simp only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, reductionScalarComplexCounit, complexCounitApp]
  erw [← he, ← quotientMap]
  change _ ≫ _ = _ ≫ _ ≫ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient _ _).map
      ((mapHomologicalComplexCompIso e (.up ℤ)).hom.app P))
  exact hd

private theorem publishedRightComp (T : Scheme.{u})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ V) :
    rightComp a b = pbcDerivedRestrictComp a b (a ≫ b) rfl := by
  have hr : resComp a b = pbcRestrictComp a b (a ≫ b) rfl := by
    apply (pbcRestrictComp_exists a b (a ≫ b) rfl).unique
    · intro M U x
      rfl
    · exact (pbcRestrictComp_exists a b (a ≫ b) rfl).exists.choose_spec
  unfold rightComp pbcDerivedRestrictComp
  rw [hr]

end AlgebraicGeometry.ProEtale
