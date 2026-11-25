/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all WeilConjectures.AlgebraicGeometry.Adic.AdicTorFlatCriterion
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCohomologyTorsionNormalForm
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.ActualCompletedReductionReconstruction
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorCohomologicalBounds
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
/-! # Integral canonical truncations and their conditional tower computation

The Roos-limit formulation retains the actual quotient transitions and makes no
choice of an unspecified derived-limit object.

## References

* Stacks Tags 0118 and 08J5
* Bhatt--Scholze 4.2.8
* Tag 07KC
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u

attribute [local instance 2000] AlgebraicGeometry.Scheme.reductionRingModulesHasDerivedCategory
attribute [local instance 2000] AlgebraicGeometry.Scheme.pbcTowers_hasDerivedCategory
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable [hNoeth : IsNoetherian T] [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
include hNoeth hDim hInv

/-- The ambient standard t-structure on completed coefficients. -/
abbrev pbcAmbientTStructure :=
  DerivedCategory.TStructure.t (C := pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))

/-- The canonical ambient truncations remain in the integral full subcategory. -/
theorem pbcIntegralCanonicalTruncations_mem
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (m : ℤ) :
    PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        (((pbcAmbientTStructure T l E).truncLE m).obj K.obj) ∧
      PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
        (((pbcAmbientTStructure T l E).truncGE m).obj K.obj) := by
  have hl : IsUnit (l : Γ(T, ⊤)) := by
    apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro t ht
    simpa using (hInv.out t)
  exact (integralStratifiedPerfectClosure T l E hDim.out hl).2.2.1 K.obj K.property m

/-- Restriction of the actual ambient lower truncation, with all ambient maps. -/
def pbcIntegralTruncLE (m : ℤ) :
    PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) ⥤
      PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
    ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
      (pbcAmbientTStructure T l E).truncLE m)
    (fun K ↦ (pbcIntegralCanonicalTruncations_mem T l E K m).1)

/-- Restriction of the actual ambient upper truncation, with all ambient maps. -/
def pbcIntegralTruncGE (m : ℤ) :
    PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) ⥤
      PbcBoundedConstructibleComplete T (pbcIntegralDatum l E) :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))
    ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))) ⋙
      (pbcAmbientTStructure T l E).truncGE m)
    (fun K ↦ (pbcIntegralCanonicalTruncations_mem T l E K m).2)

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The normalized reduction diagram, including the canonical semilinear transitions. -/
def pbcCanonicalReductionDiagram (K : PbcCompletedDerived T d) :
    ℕᵒᵖ ⥤ PbcCompletedDerived T d :=
  Functor.ofOpSequence
    (X := fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
      ((pbcCompletedReduction T d n).obj K))
    (fun n ↦ (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
      (pbcReductionTransition (pbcAdicProjection T d (n + 1))
        (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
        (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
        (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
        (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.app
          ((pbcCompletedReduction T d n).obj K))

/-- The higher-Tor vanishing formulation of the compatibility condition,
required above every cutoff. The single cohomology module is placed in degree zero. -/
def PbcTruncationTorCompatible (K : PbcCompletedDerived T d) : Prop :=
  ∀ (n : ℕ) (q p : ℤ), p < 0 →
    IsZero ((DerivedCategory.homologyFunctor _ p).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pbcCompletedReduction T d (n + 1)).obj K)))))

omit hNoeth hDim hInv in
private theorem single_kflat_iff_flat
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (M : pbcModules T R) (q : ℤ) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) R
      ((CochainComplex.singleFunctor _ q).obj M) ↔
      SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) M := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let := SheafOfModules.symmetricCategory.{u, u + 1, u + 1} R
  let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
  have (N : pbcModules T R) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft N) := by
    have :=
      SheafOfModules.tensorLeft_preservesColimits_independentCoefficients.{u + 1, u, u + 1} R N
    exact preservesColimitsOfSize_shrink _
  have (N : pbcModules T R) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight N) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ (pbcModules T R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ (pbcModules T R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (pbcModules T R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have hk (P : CochainComplex (pbcModules T R) ℤ) :
      @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      T.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) R P ↔
        (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    constructor
    · intro hP Z hZ
      obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
      rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
      have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
        (CochainComplex.mapBifunctor Z P (MonoidalCategory.curriedTensor _))).2 (hP Z hZ)
      exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso
        (BraidedCategory.braiding _ _) hr, hr⟩
    · intro hP Z hZ
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
        (hP _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).2 hZ)).2
  rw [hk]
  change (HomologicalComplex.quasiIso (pbcModules T R) (.up ℤ)).kFlat
    ((HomologicalComplex.single _ (.up ℤ) q).obj M) ↔ _
  rw [CochainComplex.kFlat_single_obj_iff_flat]
  exact ⟨fun h ↦ (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R M).symm h.2,
    SheafOfModules.flat_to_cat.{u + 1, u, u + 1} R M⟩

omit hNoeth hDim hInv in
private theorem flat_of_iso
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {M N : pbcModules T R} (e : M ≅ N)
    (h : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T) (R := R) M) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T) (R := R) N := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let tensor : MonoidalCategory (pbcModules T R) :=
    SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let e₁ := SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R M
  let e₂ := SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R N
  let e₃ := (@MonoidalCategory.curriedTensor (pbcModules T R) _ tensor).flip.mapIso e
  exact (exactFunctor _ _).prop_of_iso (e₁ ≪≫ e₃ ≪≫ e₂.symm) h

omit hNoeth hDim hInv in
private theorem extend_flat
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R)
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T) (R := R) M) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T) (R := S)
      ((pbcExtend φ).obj M) := by
  let R' := (adicLisseForget T).obj R
  let S' := (adicLisseForget T).obj S
  let N := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (J := ProEt.topology T) φ M
  obtain ⟨e⟩ := SheafOfModules.nonempty_scalarTensorComparisonOfUniverses.{u + 1, u, u + 1, u + 1}
    (J := ProEt.topology T) φ M
  have : PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := R) M) := hM.1
  have : PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := R) M) := hM.2
  have : PreservesFiniteLimits
      (pbcRestrict φ ⋙ SheafOfModules.siteSheafTensorRight
        (J := ProEt.topology T) (A := R) M ⋙ SheafOfModules.toSheaf R') := inferInstance
  have : PreservesFiniteColimits
      (pbcRestrict φ ⋙ SheafOfModules.siteSheafTensorRight
        (J := ProEt.topology T) (A := R) M ⋙ SheafOfModules.toSheaf R') := inferInstance
  have : PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := S) N ⋙ SheafOfModules.toSheaf S') :=
    preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight
      (J := ProEt.topology T) (A := S) N ⋙ SheafOfModules.toSheaf S') :=
    preservesFiniteColimits_of_natIso e
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} S') := inferInstance
  have hN : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := S) N :=
    ⟨preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf S'),
      preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf S')⟩
  exact ((pbcExtensionExistence φ).choose_spec.choose M).symm ▸ hN

omit hNoeth hDim hInv in
private def extend_single_iso
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (q : ℤ)
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T) (R := R) M) :
    (pbcDerivedExtend φ).obj ((DerivedCategory.singleFunctor _ q).obj M) ≅
      (DerivedCategory.singleFunctor _ q).obj ((pbcExtend φ).obj M) := by
  let P := (CochainComplex.singleFunctor _ q).obj M
  have hk := (single_kflat_iff_flat T M q).2 hM
  have := pbcExtensionCounit_isIso φ P hk
  exact (pbcDerivedExtend φ).mapIso ((DerivedCategory.singleFunctorIsoCompQ _ q).app M) ≪≫
    asIso ((pbcExtensionCounit φ).app ((HomotopyCategory.quotient _ _).obj P)) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (pbcExtend φ) (.up ℤ) q).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (pbcModules T S) q).app
      ((pbcExtend φ).obj M)).symm

omit hNoeth hDim hInv in
private theorem extend_isLE
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (K : DerivedCategory (pbcModules T R)) (a : ℤ) (hK : K.IsLE a) :
    ((pbcDerivedExtend φ).obj K).IsLE a := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact (SheafOfModules.ringedTensorCohomologicalBounds.{u + 2, u + 1, u + 1, u} φ a).1 K hK

omit hNoeth hDim hInv in
private theorem extend_isGE
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (K : DerivedCategory (pbcModules T R)) (a : ℤ) (hK : K.IsGE a)
    (hflat : ∀ q : ℤ, a ≤ q → SheafOfModules.IsFlatOnSite
      (J := ProEt.topology T) (R := R) ((DerivedCategory.homologyFunctor _ q).obj K)) :
    ((pbcDerivedExtend φ).obj K).IsGE a := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  apply (SheafOfModules.ringedTensorCohomologicalBounds.{u + 2, u + 1, u + 1, u} φ a).2 K hK
  intro q hq p hp
  let M := (DerivedCategory.homologyFunctor _ q).obj K
  let e := (pbcDerivedExtend φ).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm ≪≫
    extend_single_iso T φ M 0 (hflat q hq)
  exact (DerivedCategory.isZero_of_isGE
    ((DerivedCategory.singleFunctor _ 0).obj ((pbcExtend φ).obj M)) 0 (-(p : ℤ))
      (by omega)).of_iso ((DerivedCategory.homologyFunctor _ (-(p : ℤ))).mapIso e)

omit hNoeth hDim hInv in
private theorem truncGE_flat
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (K : DerivedCategory (pbcModules T R)) (a : ℤ)
    (hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology T) (R := R) ((DerivedCategory.homologyFunctor _ q).obj K)) :
    ∀ q : ℤ, a ≤ q → SheafOfModules.IsFlatOnSite
      (J := ProEt.topology T) (R := R)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((DerivedCategory.TStructure.t.truncGE a).obj K)) := by
  intro q hq
  have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K a q hq
  exact flat_of_iso T (asIso ((DerivedCategory.homologyFunctor _ q).map
    ((DerivedCategory.TStructure.t.truncGEπ a).app K))) (hflat q)

omit hNoeth hDim hInv in
private theorem extend_flat_cohomology
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (K : DerivedCategory (pbcModules T R))
    (hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology T) (R := R) ((DerivedCategory.homologyFunctor _ q).obj K))
    (q : ℤ) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T) (R := S)
      ((DerivedCategory.homologyFunctor _ q).obj ((pbcDerivedExtend φ).obj K)) := by
  let F := pbcDerivedExtend φ
  let t := DerivedCategory.TStructure.t (C := pbcModules T R)
  let L := (t.truncLE q).obj K
  let H := (t.truncGE q).obj L
  let : F.CommShift ℤ :=
    (pbcDerivedExtensionExistence φ).choose_spec.choose_spec.2.1.choose
  have hF : F.IsTriangulated :=
    (pbcDerivedExtensionExistence φ).choose_spec.choose_spec.2.1.choose_spec
  have hLE : (F.obj L).IsLE q := extend_isLE T φ L q inferInstance
  have hGE : (F.obj ((t.truncGE (q + 1)).obj K)).IsGE (q + 1) :=
    extend_isGE T φ _ _ inferInstance (truncGE_flat T K _ hflat)
  have hLE' : (F.obj L).IsLE (q + 1 - 1) := by simpa using hLE
  have hι : IsIso ((DerivedCategory.homologyFunctor _ q).map
      (F.map ((t.truncLEι q).app K))) := by
    have : ((F.mapTriangle.obj ((t.triangleLTGE (q + 1)).obj K)).obj₁).IsLE
        (q + 1 - 1) := hLE'
    have : ((F.mapTriangle.obj ((t.triangleLTGE (q + 1)).obj K)).obj₃).IsGE
        (q + 1) := hGE
    exact DerivedCategory.isIso_homologyFunctor_map_mor₁_of_isLE_of_isGE
      (F.mapTriangle.obj ((t.triangleLTGE (q + 1)).obj K))
      (F.map_distinguished _ (t.triangleLTGE_distinguished (q + 1) K))
      (q + 1) q (by omega)
  have hlow : (F.obj ((t.truncLT q).obj L)).IsLE (q - 1) :=
    extend_isLE T φ _ _ inferInstance
  have hπ : IsIso ((DerivedCategory.homologyFunctor _ q).map
      (F.map ((t.truncGEπ q).app L))) := by
    have : ((F.mapTriangle.obj ((t.triangleLTGE q).obj L)).obj₁).IsLE (q - 1) := hlow
    exact DerivedCategory.isIso_homologyMap_mor₂
      (F.mapTriangle.obj ((t.triangleLTGE q).obj L))
      (F.map_distinguished _ (t.triangleLTGE_distinguished q L)) q (q + 1) rfl
      (DerivedCategory.isZero_of_isLE _ (q - 1) q (by omega))
      (DerivedCategory.isZero_of_isLE _ (q - 1) (q + 1) (by omega))
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE H q
  have hι₀ : IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((t.truncLEι q).app K)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K (q + 1) q (by omega)
  have hπ₀ := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app L q q le_rfl
  let eM : (DerivedCategory.homologyFunctor _ q).obj K ≅ M :=
    (asIso ((DerivedCategory.homologyFunctor _ q).map
      ((t.truncLEι q).app K))).symm ≪≫
    asIso ((DerivedCategory.homologyFunctor _ q).map ((t.truncGEπ q).app L)) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app M
  have hM := flat_of_iso T eM (hflat q)
  let eout : (DerivedCategory.homologyFunctor _ q).obj (F.obj K) ≅
      (pbcExtend φ).obj M :=
    (asIso ((DerivedCategory.homologyFunctor _ q).map
      (F.map ((t.truncLEι q).app K)))).symm ≪≫
    asIso ((DerivedCategory.homologyFunctor _ q).map (F.map ((t.truncGEπ q).app L))) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      (F.mapIso e ≪≫ extend_single_iso T φ M q hM) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app _
  exact flat_of_iso T eout.symm (extend_flat T φ M hM)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
omit hNoeth hDim hInv in
private theorem map_truncations
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (F : DerivedCategory (pbcModules T R) ⥤ DerivedCategory (pbcModules T S))
    [F.CommShift ℤ] [F.IsTriangulated]
    (K : DerivedCategory (pbcModules T R)) (m : ℤ)
    (hLE : (F.obj ((DerivedCategory.TStructure.t.truncLE m).obj K)).IsLE m)
    (hGE : (F.obj ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K)).IsGE
      (m + 1)) :
    (∃ e : F.obj ((DerivedCategory.TStructure.t.truncLE m).obj K) ≅
        (DerivedCategory.TStructure.t.truncLE m).obj (F.obj K),
      e.hom ≫ (DerivedCategory.TStructure.t.truncLEι m).app
          (F.obj K) =
        F.map ((DerivedCategory.TStructure.t.truncLEι m).app K)) ∧
    (∃ e : F.obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K) ≅
        (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (F.obj K),
      F.map ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app K) ≫
        e.hom = (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app
          (F.obj K)) := by
  let t := DerivedCategory.TStructure.t (C := pbcModules T R)
  let s := DerivedCategory.TStructure.t (C := pbcModules T S)
  obtain ⟨e, he⟩ := s.triangle_iso_exists
    (F.map_distinguished _ (t.triangleLTGE_distinguished (m + 1) K))
    (s.triangleLTGE_distinguished (m + 1) (F.obj K)) (Iso.refl _) m (m + 1)
    hLE hGE (by
      change s.IsLE ((s.truncLT (m + 1)).obj (F.obj K)) m
      exact s.isLE_truncLT_obj _ _ _ (by omega)) inferInstance
  refine ⟨⟨CategoryTheory.Pretriangulated.Triangle.π₁.mapIso e, ?_⟩,
    ⟨CategoryTheory.Pretriangulated.Triangle.π₃.mapIso e, ?_⟩⟩
  · have he' : e.hom.hom₂ = 𝟙 (F.obj K) := he
    calc
      _ = F.map ((t.truncLEι m).app K) ≫ e.hom.hom₂ := e.hom.comm₁.symm
      _ = _ := by rw [he']; exact Category.comp_id _
  · have he' : e.hom.hom₂ = 𝟙 (F.obj K) := he
    calc
      _ = e.hom.hom₂ ≫ (s.truncGEπ (m + 1)).app (F.obj K) := e.hom.comm₂
      _ = _ := by rw [he']; exact Category.id_comp _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
omit hNoeth hDim hInv in
private theorem extend_truncations
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (K : DerivedCategory (pbcModules T R)) (m : ℤ)
    (hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology T) (R := R) ((DerivedCategory.homologyFunctor _ q).obj K)) :
    (∃ e : (pbcDerivedExtend φ).obj ((DerivedCategory.TStructure.t.truncLE m).obj K) ≅
        (DerivedCategory.TStructure.t.truncLE m).obj ((pbcDerivedExtend φ).obj K),
      e.hom ≫ (DerivedCategory.TStructure.t.truncLEι m).app
          ((pbcDerivedExtend φ).obj K) =
        (pbcDerivedExtend φ).map ((DerivedCategory.TStructure.t.truncLEι m).app K)) ∧
    (∃ e : (pbcDerivedExtend φ).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K) ≅
        (DerivedCategory.TStructure.t.truncGE (m + 1)).obj ((pbcDerivedExtend φ).obj K),
      (pbcDerivedExtend φ).map ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app K) ≫
        e.hom = (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app
          ((pbcDerivedExtend φ).obj K)) := by
  let F := pbcDerivedExtend φ
  let : F.CommShift ℤ :=
    (pbcDerivedExtensionExistence φ).choose_spec.choose_spec.2.1.choose
  have : F.IsTriangulated :=
    (pbcDerivedExtensionExistence φ).choose_spec.choose_spec.2.1.choose_spec
  exact map_truncations T F K m
    (extend_isLE T φ _ m inferInstance)
    (extend_isGE T φ _ (m + 1) inferInstance (truncGE_flat T K _ hflat))

omit hNoeth hDim hInv in
/-- Flat cohomology is sufficient for the compatibility used in the theorem.
The single complex in degree zero expresses flatness by K-flatness and uses the
actual completed ring, rather than the underlying constant coefficient ring. -/
theorem pbc_flat_cohomology_torCompatible (K : PbcCompletedDerived T d)
    (_hflat : ∀ i : ℤ, CochainComplex.IsKFlatIndependentCoefficients
      (R := pbcAdicCompletion T d)
      ((CochainComplex.singleFunctor _ 0).obj
        ((DerivedCategory.homologyFunctor _ i).obj K))) :
    PbcTruncationTorCompatible T d K := by
  intro n q p hp
  have hflat (i : ℤ) := (single_kflat_iff_flat T
    ((DerivedCategory.homologyFunctor _ i).obj K) 0).1 (_hflat i)
  have hred := extend_flat_cohomology T (pbcAdicProjection T d (n + 1)) K hflat q
  let M := (DerivedCategory.homologyFunctor _ q).obj
    ((pbcCompletedReduction T d (n + 1)).obj K)
  let φ := pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)
  let e := extend_single_iso T φ M 0 hred
  exact (DerivedCategory.isZero_of_isGE
    ((DerivedCategory.singleFunctor _ 0).obj ((pbcExtend φ).obj M)) 0 p hp).of_iso
      ((DerivedCategory.homologyFunctor _ p).mapIso e)

/-- On the integral constructible category, the all-level compatibility condition
is equivalent to flat cohomology of the local models.
Flatness is expressed by K-flatness of each actual cohomology module in degree zero. -/
theorem pbc_torCompatible_iff_flat_cohomology
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) :
    PbcTruncationTorCompatible T (pbcIntegralDatum l E) K.obj ↔
      ∀ i : ℤ, CochainComplex.IsKFlatIndependentCoefficients
        (R := pbcAdicCompletion T (pbcIntegralDatum l E))
        ((CochainComplex.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ i).obj K.obj)) := by
  constructor
  · intro hTor q
    apply (single_kflat_iff_flat T _ 0).2
    obtain ⟨S, V, h⟩ := pbc_integral_cohomology_torsion_normal_form T hDim.out l E
      hInv.out K q
    apply flat_of_stratum_cover T S V
    intro a j
    obtain ⟨r, F, N, hfree, ⟨e⟩, f, hf, n, t, ht⟩ := h a j
    have hz := hTor n q (-1) (by omega)
    have : Epi t := ht
    have hc : IsZero (cokernel f.asHom) := by
      apply IsZero.of_epi t
      apply Functor.map_isZero
      apply Functor.map_isZero
      exact hz
    have hN := isZero_of_nilpotent_cokernel f hf hc
    have hF : SheafOfModules.IsFlatOnSite (J := ProEt.topology ((V a).X j))
        (R := (adicTowerInverseImage ((V a).f j ≫ S.immersion a)).obj
          (pbcAdicCompletion T (pbcIntegralDatum l E))) F := by
      apply flat_of_sectionwise_flat
      intro U
      have : Module.Free _ (F.val.obj U) := Module.Free.of_basis (Classical.choice (hfree U))
      infer_instance
    exact flat_of_iso _ ((e ≪≫ (isoBiprodZero hN).symm).symm) hF
  · exact pbc_flat_cohomology_torCompatible T (pbcIntegralDatum l E) K.obj

omit hNoeth hDim hInv in
/-- Exact countable products for modules over the actual completed coefficient sheaf. -/
theorem pbcCompletedCountableAB4Star : CountableAB4Star
    (pbcModules T (pbcAdicCompletion T d)) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  have : HasCountableProducts (pbcModules T (pbcAdicCompletion T d)) :=
    (ProEt.countableProducts_exact.{u, u, 0} T (pbcAdicCompletion T d)).1
  have : (lim (J := Discrete ℕ)
      (C := pbcModules T (pbcAdicCompletion T d))).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (ProEt.countableProducts_exact.{u, u, 0} T
          (pbcAdicCompletion T d)).2.2 ℕ (fun n ↦ F.obj ⟨n⟩)
            (fun n ↦ G.obj ⟨n⟩) (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have : HasFiniteBiproducts (pbcModules T (pbcAdicCompletion T d)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have := hasExactLimitsOfShape_of_preservesEpi
    (pbcModules T (pbcAdicCompletion T d)) (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat _

/-- Countable products in the ambient derived category, fixed by their limit property. -/
instance pbcCompletedDerivedCountableProducts : HasCountableProducts
    (PbcCompletedDerived T d) :=
  letI := pbcCompletedCountableAB4Star T d
  (derivedCategory_countableProducts_core.{0}
    (pbcModules T (pbcAdicCompletion T d))).choose

omit hNoeth hDim hInv in
private theorem restricted_extend_truncations
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (K : DerivedCategory (pbcModules T R)) (m : ℤ)
    (hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology T) (R := R) ((DerivedCategory.homologyFunctor _ q).obj K)) :
    let G := pbcDerivedExtend φ ⋙ pbcDerivedRestrict φ
    (∃ e : G.obj ((DerivedCategory.TStructure.t.truncLE m).obj K) ≅
        (DerivedCategory.TStructure.t.truncLE m).obj (G.obj K),
      e.hom ≫ (DerivedCategory.TStructure.t.truncLEι m).app (G.obj K) =
        G.map ((DerivedCategory.TStructure.t.truncLEι m).app K)) ∧
    (∃ e : G.obj ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K) ≅
        (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (G.obj K),
      G.map ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app K) ≫ e.hom =
        (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (G.obj K)) := by
  let F := pbcDerivedExtend φ
  let : F.CommShift ℤ :=
    (pbcDerivedExtensionExistence φ).choose_spec.choose_spec.2.1.choose
  have : F.IsTriangulated :=
    (pbcDerivedExtensionExistence φ).choose_spec.choose_spec.2.1.choose_spec
  have hLE := extend_isLE T φ
    ((DerivedCategory.TStructure.t.truncLE m).obj K) m inferInstance
  have hGE := extend_isGE T φ
    ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K) (m + 1)
    inferInstance (truncGE_flat T K _ hflat)
  have : (pbcDerivedRestrict φ).IsTriangulated :=
    inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.IsTriangulated)
  exact map_truncations T (F ⋙ pbcDerivedRestrict φ) K m
    ((pbcRestrict φ).isLE_mapDerivedCategory_obj _ m)
    ((pbcRestrict φ).isGE_mapDerivedCategory_obj _ (m + 1))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
omit hNoeth hDim hInv in
private theorem reduction_transition_natural
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    {K L : DerivedCategory (pbcModules T R)} (f : K ⟶ L) :
    (pbcDerivedExtend φ).map f ≫ pbcReductionTransition φ ψ χ h L =
      pbcReductionTransition φ ψ χ h K ≫
        (pbcDerivedRestrict ψ).map ((pbcDerivedExtend χ).map f) := by
  let a := pbcDerivedScalarAdjunction φ
  apply (a.homEquiv K _).injective
  dsimp only [pbcReductionTransition]
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  have hn := (pbcDerivedRestrictComp φ ψ χ h).inv.naturality
    ((pbcDerivedExtend χ).map f)
  dsimp only [Functor.comp_map] at hn
  have hu := (pbcDerivedScalarAdjunction χ).unit.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← hn, ← Category.assoc, hu, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
omit hNoeth hDim hInv in
private theorem reduction_diagram_natural
    {K L : PbcCompletedDerived T d} (f : K ⟶ L) (n : ℕ) :
    (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
        ((pbcCompletedReduction T d (n + 1)).map f) ≫
      (pbcCanonicalReductionDiagram T d L).map (homOfLE (Nat.le_succ n)).op =
    (pbcCanonicalReductionDiagram T d K).map (homOfLE (Nat.le_succ n)).op ≫
      (pbcDerivedRestrict (pbcAdicProjection T d n)).map
        ((pbcCompletedReduction T d n).map f) := by
  simp only [pbcCanonicalReductionDiagram, Functor.ofOpSequence_map_homOfLE_succ]
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [reduction_transition_natural T]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
    (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
    (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n))).hom.naturality
      ((pbcCompletedReduction T d n).map f)
  dsimp only [Functor.comp_map] at hn
  rw [hn]

omit hNoeth hDim hInv in
private theorem derived_limit_transport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {X Y : ℕ → C} [HasProduct X] [HasProduct Y]
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    (L : C) (hL : IsDerivedLimit f L) (a : ∀ n, X n ≅ Y n)
    (ha : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n) :
    IsDerivedLimit g L := by
  obtain ⟨p, δ, hδ⟩ := hL
  let A : (∏ᶜ X) ≅ (∏ᶜ Y) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨p ≫ A.hom, A.inv ≫ δ, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl L) A.symm A.symm ?_ ?_ ?_
  · change (p ≫ A.hom) ≫ A.inv = 𝟙 L ≫ p
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · exact (towerTransitionEndomorphism_natural_backward g f
      (fun n ↦ (a n).inv) (fun n ↦ by
        apply (cancel_mono (a n).hom).1
        simpa [Category.assoc] using
          congrArg (fun k ↦ (a (n + 1)).inv ≫ k) (ha n))).symm
  · change (A.inv ≫ δ) ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 L) = A.inv ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Under exactly the higher-Tor compatibility condition at all levels, canonical
integral truncations are the derived limits of the levelwise truncated reduction tower.
Their quotient reductions are canonically the quotient-coefficient truncations: the
comparison isomorphisms are normalized by the truncation counit and unit. -/
theorem pbc_integral_truncations
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E))
    (_hTor : PbcTruncationTorCompatible T (pbcIntegralDatum l E) K.obj) (m : ℤ) :
    IsDerivedLimit
      (K := fun n ↦ ((pbcAmbientTStructure T l E).truncLE m).obj
        ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).obj (op n)))
      (fun n ↦ ((pbcAmbientTStructure T l E).truncLE m).map
        ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).map
          (homOfLE (Nat.le_succ n)).op))
      (((pbcAmbientTStructure T l E).truncLE m).obj K.obj) ∧
    IsDerivedLimit
      (K := fun n ↦ ((pbcAmbientTStructure T l E).truncGE (m + 1)).obj
        ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).obj (op n)))
      (fun n ↦ ((pbcAmbientTStructure T l E).truncGE (m + 1)).map
        ((pbcCanonicalReductionDiagram T (pbcIntegralDatum l E) K.obj).map
          (homOfLE (Nat.le_succ n)).op))
      (((pbcAmbientTStructure T l E).truncGE (m + 1)).obj K.obj) ∧
    ∀ n : ℕ,
      (∃ e : (pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
          (((pbcAmbientTStructure T l E).truncLE m).obj K.obj) ≅
          (DerivedCategory.TStructure.t.truncLE m).obj
            ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K.obj),
        e.hom ≫ (DerivedCategory.TStructure.t.truncLEι m).app
            ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K.obj) =
          (pbcCompletedReduction T (pbcIntegralDatum l E) n).map
            (((pbcAmbientTStructure T l E).truncLEι m).app K.obj)) ∧
      (∃ e : (pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
          (((pbcAmbientTStructure T l E).truncGE (m + 1)).obj K.obj) ≅
          (DerivedCategory.TStructure.t.truncGE (m + 1)).obj
            ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K.obj),
        (pbcCompletedReduction T (pbcIntegralDatum l E) n).map
            (((pbcAmbientTStructure T l E).truncGEπ (m + 1)).app K.obj) ≫ e.hom =
          (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app
            ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K.obj)) := by
  let d := pbcIntegralDatum l E
  let t := pbcAmbientTStructure T l E
  have hflat (q : ℤ) := (single_kflat_iff_flat T
    ((DerivedCategory.homologyFunctor _ q).obj K.obj) 0).1
      ((pbc_torCompatible_iff_flat_cohomology T l E K).mp _hTor q)
  have hmem := pbcIntegralCanonicalTruncations_mem T l E K m
  have hmem' := pbcIntegralCanonicalTruncations_mem T l E K (m + 1)
  have hLE := pbc_actual_completed_reduction_reconstruction T d
    ((t.truncLE m).obj K.obj) hmem.1.1
  have hGE := pbc_actual_completed_reduction_reconstruction T d
    ((t.truncGE (m + 1)).obj K.obj) hmem'.2.1
  let ML := pbcCanonicalReductionDiagram T d ((t.truncLE m).obj K.obj)
  let MU := pbcCanonicalReductionDiagram T d ((t.truncGE (m + 1)).obj K.obj)
  change IsDerivedLimit (K := fun n ↦ ML.obj (op n))
    (fun n ↦ ML.map (homOfLE (Nat.le_succ n)).op) ((t.truncLE m).obj K.obj) at hLE
  change IsDerivedLimit (K := fun n ↦ MU.obj (op n))
    (fun n ↦ MU.map (homOfLE (Nat.le_succ n)).op)
      ((t.truncGE (m + 1)).obj K.obj) at hGE
  let M := pbcCanonicalReductionDiagram T d K.obj
  choose eLE heLE using fun n : ℕ ↦
    (restricted_extend_truncations T (pbcAdicProjection T d n) K.obj m hflat).1
  choose eGE heGE using fun n : ℕ ↦
    (restricted_extend_truncations T (pbcAdicProjection T d n) K.obj m hflat).2
  change ∀ n, ML.obj (op n) ≅ (t.truncLE m).obj (M.obj (op n)) at eLE
  change ∀ n, MU.obj (op n) ≅ (t.truncGE (m + 1)).obj (M.obj (op n)) at eGE
  change ∀ n, (eLE n).hom ≫ (t.truncLEι m).app (M.obj (op n)) =
    (pbcDerivedRestrict (pbcAdicProjection T d n)).map
      ((pbcCompletedReduction T d n).map ((t.truncLEι m).app K.obj)) at heLE
  change ∀ n, (pbcDerivedRestrict (pbcAdicProjection T d n)).map
      ((pbcCompletedReduction T d n).map ((t.truncGEπ (m + 1)).app K.obj)) ≫
    (eGE n).hom = (t.truncGEπ (m + 1)).app (M.obj (op n)) at heGE
  refine ⟨?_, ?_, ?_⟩
  · apply derived_limit_transport _ _ _ hLE eLE
    intro n
    have : t.IsLE ((pbcCanonicalReductionDiagram T d
        ((t.truncLE m).obj K.obj)).obj (op (n + 1))) ((m + 1) - 1) := by
      rw [show m + 1 - 1 = m by omega]
      exact t.isLE_of_iso (eLE (n + 1)).symm m
    apply t.to_truncLT_obj_ext (n := m + 1)
    change (ML.map (homOfLE (Nat.le_succ n)).op ≫ (eLE n).hom) ≫
        (t.truncLEι m).app (M.obj (op n)) =
      ((eLE (n + 1)).hom ≫ (t.truncLE m).map
        (M.map (homOfLE (Nat.le_succ n)).op)) ≫
          (t.truncLEι m).app (M.obj (op n))
    have hn := (t.truncLEι m).naturality (M.map (homOfLE (Nat.le_succ n)).op)
    dsimp only [Functor.id_map] at hn
    simp only [Category.assoc]
    rw [heLE n, hn]
    rw [← Category.assoc, heLE (n + 1)]
    exact (reduction_diagram_natural T d ((t.truncLEι m).app K.obj) n).symm
  · apply derived_limit_transport _ _ _ hGE eGE
    intro n
    apply (cancel_epi (eGE (n + 1)).inv).1
    apply t.from_truncGE_obj_ext (n := m + 1)
    have hn : (t.truncGEπ (m + 1)).app (M.obj (op (n + 1))) ≫
        (eGE (n + 1)).inv =
      (pbcDerivedRestrict (pbcAdicProjection T d (n + 1))).map
        ((pbcCompletedReduction T d (n + 1)).map
          ((t.truncGEπ (m + 1)).app K.obj)) := by
      apply (cancel_mono (eGE (n + 1)).hom).1
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
        (heGE (n + 1)).symm
    simp only [← Category.assoc, hn]
    rw [reduction_diagram_natural T d ((t.truncGEπ (m + 1)).app K.obj) n]
    simp only [Category.assoc, heGE]
    exact (t.truncGEπ (m + 1)).naturality (M.map (homOfLE (Nat.le_succ n)).op)
  · intro n
    exact extend_truncations T (pbcAdicProjection T d n) K.obj m hflat

end AlgebraicGeometry.Scheme
