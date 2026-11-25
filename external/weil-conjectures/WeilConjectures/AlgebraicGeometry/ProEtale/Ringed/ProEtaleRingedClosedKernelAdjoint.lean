/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # The arbitrary-ring-sheaf closed support adjoint

## References

* Stacks, Tags 09AA, 09BM, 09BN, 09AH, 070I, 070K, 08BJ and 079P
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The natural kernel of the open adjunction unit, formed in the functor category.
Evaluation identifies it with `ker(N → j_*j^*N)`, including the kernel inclusion. -/
noncomputable def ringedSupportKernel {X U : Scheme.{u}} (j : U ⟶ X)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aj : proEtaleModuleInverseImage j B ⊣ proEtaleRingedDirectImage j B) :
    proEtaleRingModules X B ⥤ proEtaleRingModules X B :=
  kernel aj.unit

/-- The closed inverse image of the support kernel: the actual underived `i!_0`. -/
noncomputable def ringedClosedKernelShriek {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aj : proEtaleModuleInverseImage j B ⊣ proEtaleRingedDirectImage j B) :=
  ringedSupportKernel j B aj ⋙ proEtaleModuleInverseImage i B

/-- The specified computation on any K-injective resolution, obtained by localizing
its quasi-isomorphism and using the canonical K-injective derived comparison. -/
noncomputable def ringedClosedKernelResolutionIso {X Z U : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (aj : proEtaleModuleInverseImage j B ⊣ proEtaleRingedDirectImage j B)
    [(ringedClosedKernelShriek i j B aj).Additive]
    {K I : CochainComplex (proEtaleRingModules X B) ℤ}
    (r : K ⟶ I) [QuasiIso r] [I.IsKInjective] :
    (ringedClosedKernelShriek i j B aj).rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((ringedClosedKernelShriek i j B aj).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
  (ringedClosedKernelShriek i j B aj).rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map r)) ≪≫
    (ringedClosedKernelShriek i j B aj).rightDerivedFunctorObjQIso I

-- Lift maps uniquely through the support inclusion, then use full faithfulness.
private noncomputable def kernelAdjunction
    {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) [R.Full] [R.Faithful] (H : D ⥤ D) (T : D ⥤ C)
    (k : H ⟶ 𝟭 D) [∀ N, Mono (k.app N)] (e : H ≅ T ⋙ R)
    (hf : ∀ (P : C) (N : D) (f : R.obj P ⟶ N),
      ∃ g : R.obj P ⟶ H.obj N, g ≫ k.app N = f) : R ⊣ T := by
  let f (P : C) (N : D) (g : P ⟶ T.obj N) : R.obj P ⟶ N :=
    R.map g ≫ e.inv.app N ≫ k.app N
  have hb (P : C) (N : D) : Function.Bijective (f P N) := by
    constructor
    · intro a b hab
      apply R.map_injective
      apply (cancel_mono (e.inv.app N)).1
      apply (cancel_mono (k.app N)).1
      simpa only [f, Category.assoc] using hab
    · intro a
      obtain ⟨g, hg⟩ := hf P N a
      refine ⟨R.preimage (g ≫ e.hom.app N), ?_⟩
      simp only [f, R.map_preimage, Category.assoc, Iso.hom_inv_id_app_assoc, hg]
  let E (P : C) (N : D) := (Equiv.ofBijective (f P N) (hb P N)).symm
  refine Adjunction.mkOfHomEquiv
    { homEquiv := E
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro P P' N a b
    change f P N (a ≫ b) = R.map a ≫ f P' N b
    simp only [f, R.map_comp, Category.assoc]
  · intro P N N' a b
    apply (E P N').symm.injective
    change f P N' (E P N' (a ≫ b)) = f P N' (E P N a ≫ T.map b)
    rw [show f P N' (E P N' (a ≫ b)) = a ≫ b from
      (E P N').symm_apply_apply _]
    change a ≫ b = R.map (E P N a ≫ T.map b) ≫ e.inv.app N' ≫ k.app N'
    rw [R.map_comp, Category.assoc]
    have hn : R.map (T.map b) ≫ e.inv.app N' = e.inv.app N ≫ H.map b :=
      e.inv.naturality b
    rw [reassoc_of% hn]
    change a ≫ b = R.map (E P N a) ≫ e.inv.app N ≫ H.map b ≫ k.app N'
    rw [k.naturality]
    have ha : f P N (E P N a) = a := (E P N).symm_apply_apply a
    simpa only [f, Category.assoc, Functor.id_map] using congrArg (· ≫ b) ha.symm

private theorem kernelAdjunction_counit
    {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) [R.Full] [R.Faithful] (H : D ⥤ D) (T : D ⥤ C)
    (k : H ⟶ 𝟭 D) [∀ N, Mono (k.app N)] (e : H ≅ T ⋙ R)
    (hf : ∀ (P : C) (N : D) (f : R.obj P ⟶ N),
      ∃ g : R.obj P ⟶ H.obj N, g ≫ k.app N = f) :
    e.hom ≫ (kernelAdjunction R H T k e hf).counit = k := by
  ext N
  change e.hom.app N ≫ (R.map (𝟙 (T.obj N)) ≫ e.inv.app N ≫ k.app N) = k.app N
  simp

-- Localize the termwise adjunction; this also fixes its counit comparison.
private noncomputable def exactDerivedAdjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory := by
  let : CatCommSq (L.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q L.mapDerivedCategory :=
    ⟨L.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (R.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q R.mapDerivedCategory :=
    ⟨R.mapDerivedCategoryFactors.symm⟩
  exact (a.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) _ _

private theorem exactDerivedAdjunction_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (I : CochainComplex D ℤ) :
    (exactDerivedAdjunction a).counit.app (DerivedCategory.Q.obj I) =
      L.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app I) ≫
        L.mapDerivedCategoryFactors.hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I) := by
  let : CatCommSq (L.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q L.mapDerivedCategory :=
    ⟨L.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (R.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q R.mapDerivedCategory :=
    ⟨R.mapDerivedCategoryFactors.symm⟩
  exact Adjunction.localization_counit_app _ _ _ _ _ _ _ _

private theorem exactDerivedAdjunction_counit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    [IsIso a.counit] (P : DerivedCategory D) :
    IsIso ((exactDerivedAdjunction a).counit.app P) := by
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Q.objObjPreimageIso P)]
  rw [exactDerivedAdjunction_counit]
  have (n : ℤ) : IsIso
      (((a.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
        (DerivedCategory.Q.objPreimage P)).f n) := by
    rw [Adjunction.mapHomologicalComplex_counit_app_f]
    infer_instance
  have : IsIso ((a.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app
      (DerivedCategory.Q.objPreimage P)) := HomologicalComplex.Hom.isIso_of_components _
  infer_instance

-- Expand the derived counit on a K-injective using its invertible derived unit.
private theorem rightDerivedAdjunction_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (a : L ⊣ R)
    (I : CochainComplex D ℤ) [I.IsKInjective] :
    a.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      L.mapDerivedCategory.map (R.rightDerivedFunctorObjQIso I).hom ≫
        L.mapDerivedCategoryFactors.hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I) := by
  let J := (HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj I
  let d := a.mapDerivedCategoryRightDerivedAdjunction
  have ht := (a.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (ComplexShape.up ℤ))
    L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit J
  change L.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app J) ≫
    d.counit.app (DerivedCategory.Qh.obj J) = _ at ht
  have he : d.counit.app (DerivedCategory.Qh.obj J) =
      L.mapDerivedCategory.map (inv (R.rightDerivedFunctorUnit.app J)) ≫
        L.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory _).obj J) ≫
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app J) := by
    apply (cancel_epi (L.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app J))).1
    simpa only [← L.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id,
      L.mapDerivedCategory.map_id, Category.id_comp] using ht
  calc
    _ = L.mapDerivedCategory.map
          (R.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso D).inv.app I)) ≫
        d.counit.app (DerivedCategory.Qh.obj J) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app I := by
      have hn : L.mapDerivedCategory.map
          (R.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso D).inv.app I)) ≫
          d.counit.app (DerivedCategory.Qh.obj J) =
          d.counit.app (DerivedCategory.Q.obj I) ≫
            (DerivedCategory.quotientCompQhIso D).inv.app I :=
        d.counit.naturality _
      rw [reassoc_of% hn]
      simp [d]
    _ = _ := by
      rw [he]
      rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
      erw [L.mapDerivedCategoryFactorsh_hom_app]
      simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
        Iso.app_hom, asIso_inv,
        Functor.map_comp, Category.assoc]
      dsimp only [J, Functor.mapIso]
      simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
      dsimp
      simp only [HomotopyCategory.quotient_obj_as]
      simp only [DerivedCategory.quotientCompQhIso_hom_naturality]
      erw [DerivedCategory.Qh.map_id]
      simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]

private theorem rightDerivedAdjunction_counit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (a : L ⊣ R)
    [IsIso a.counit] (P : DerivedCategory D) :
    IsIso (a.mapDerivedCategoryRightDerivedAdjunction.counit.app P) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective P
  rw [NatTrans.isIso_app_iff_of_iso _ e, rightDerivedAdjunction_counit]
  have (n : ℤ) : IsIso
      (((a.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I).f n) := by
    rw [Adjunction.mapHomologicalComplex_counit_app_f]
    infer_instance
  have : IsIso ((a.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I) :=
    HomologicalComplex.Hom.isIso_of_components _
  infer_instance

private theorem rightDerivedAdjunction_counit_resolution
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (a : L ⊣ R)
    {K I : CochainComplex D ℤ} (r : K ⟶ I) [QuasiIso r] [I.IsKInjective] :
    a.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj K) =
      L.mapDerivedCategory.map
          (R.rightDerivedFunctor.map (DerivedCategory.Q.map r) ≫
            (R.rightDerivedFunctorObjQIso I).hom) ≫
        L.mapDerivedCategoryFactors.hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I) ≫
        inv (DerivedCategory.Q.map r) := by
  have hn := a.mapDerivedCategoryRightDerivedAdjunction.counit.naturality
    (DerivedCategory.Q.map r)
  apply (cancel_mono (DerivedCategory.Q.map r)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [← hn, rightDerivedAdjunction_counit]
  simp only [Functor.map_comp, Category.assoc]

-- Exact restriction kills the support kernel, so its closed unit is invertible.
private theorem closedKernelConstruction
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    {L : D ⥤ C} {R : C ⥤ D} {J : D ⥤ E} {K : E ⥤ D}
    [L.Additive] [R.Additive] [J.Additive] [K.Additive]
    [PreservesFiniteLimits J] (ai : L ⊣ R) (aj : J ⊣ K)
    [IsIso ai.counit] [IsIso aj.counit]
    (hs : ∀ N, IsZero (J.obj N) → IsIso (ai.unit.app N))
    (hz : ∀ P, IsZero (J.obj (R.obj P))) :
    ∃ (_ : (kernel aj.unit ⋙ L).Additive) (a0 : R ⊣ kernel aj.unit ⋙ L)
      (eH : kernel aj.unit ≅ (kernel aj.unit ⋙ L) ⋙ R),
      eH.hom = Functor.whiskerLeft (kernel aj.unit) ai.unit ∧
        eH.hom ≫ a0.counit = kernel.ι aj.unit := by
  classical
  have := ai.fullyFaithfulROfIsIsoCounit.full
  have := ai.fullyFaithfulROfIsIsoCounit.faithful
  let H := kernel aj.unit
  let k : H ⟶ 𝟭 D := kernel.ι aj.unit
  have hk (N : D) : IsLimit (KernelFork.ofι (k.app N)
      (congr_app (kernel.condition aj.unit) N)) :=
    KernelFork.mapIsLimit _ (kernelIsKernel aj.unit)
      ((CategoryTheory.evaluation _ _).obj N)
  have (N : D) : Mono (k.app N) := Fork.IsLimit.mono (hk N)
  have hJH (N : D) : IsZero (J.obj (H.obj N)) := by
    have : IsIso (J.map (aj.unit.app N)) := by
      have : IsIso (J.map (aj.unit.app N) ≫ aj.counit.app _) := by
        exact (aj.left_triangle_components N).symm ▸
          (inferInstance : IsIso (𝟙 (J.obj N)))
      exact IsIso.of_isIso_comp_right _ (aj.counit.app _)
    exact KernelFork.IsLimit.isZero_of_mono (KernelFork.mapIsLimit _ (hk N) J)
  have : ∀ N, IsIso ((Functor.whiskerLeft H ai.unit).app N) := fun N ↦ hs _ (hJH N)
  have : IsIso (Functor.whiskerLeft H ai.unit) := NatIso.isIso_of_isIso_app _
  let eH : H ≅ (H ⋙ L) ⋙ R := asIso (Functor.whiskerLeft H ai.unit)
  have hf (P : C) (N : D) (f : R.obj P ⟶ N) :
      ∃ g : R.obj P ⟶ H.obj N, g ≫ k.app N = f := by
    have hzero : f ≫ aj.unit.app N = 0 := by
      change (𝟭 D).map f ≫ aj.unit.app N = 0
      rw [aj.unit.naturality f]
      change aj.unit.app _ ≫ K.map (J.map f) = 0
      rw [(hz P).eq_of_src (J.map f) 0, Functor.map_zero, comp_zero]
    let g := KernelFork.IsLimit.lift' (hk N) f hzero
    exact ⟨g.1, g.2⟩
  let a0 := kernelAdjunction R H (H ⋙ L) k eH hf
  have : (H ⋙ L).Additive := a0.right_adjoint_additive
  exact ⟨inferInstance, a0, eH, rfl, kernelAdjunction_counit _ _ _ _ _ _⟩

private theorem supportedUnitIso
    {C D S : Type*} [Category C] [Category D] [Category S]
    [Abelian C] [Abelian D] [Abelian S]
    {L : D ⥤ C} {R : C ⥤ D} {V : D ⥤ S} {F : S ⥤ D}
    [F.Additive] (ai : L ⊣ R) (ab : F ⊣ V)
    (hs : ∀ N, Epi (ai.unit.app N) ∧
      (ComposableArrows.mk₂ (ab.counit.app N) (ai.unit.app N)).Exact)
    (N : D) (hzero : IsZero (V.obj N)) : IsIso (ai.unit.app N) := by
  have := (hs N).1
  let T := ComposableArrows.mk₂ (ab.counit.app N) (ai.unit.app N)
  have ht : T.Exact := (hs N).2
  have he := (T.exact₂_iff ht.toIsComplex).1 ht
  have : Mono (ai.unit.app N) := he.mono_g ((F.map_isZero hzero).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- Closed support for arbitrary ring-sheaf coefficients, and all four ambient derived
adjunctions. The comparison with the kernel and the K-injective counit formula fix the
ordinary and derived counits. All module categories use the original small pro-etale
sites, with object universe `u+1`, morphism universe `u`, and module universe `u+1`. -/
theorem proEtale_ringed_closed_kernel_adjoint {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ (ai : proEtaleModuleInverseImage i B ⊣ proEtaleRingedDirectImage i B)
      (aj : proEtaleModuleInverseImage U.hom B ⊣ proEtaleRingedDirectImage U.hom B)
      (_ : (proEtaleModuleInverseImage i B).Additive)
      (_ : (proEtaleModuleInverseImage U.hom B).Additive)
      (_ : (proEtaleRingedDirectImage i B).Additive)
      (_ : (proEtaleRingedDirectImage U.hom B).Additive)
      (_ : PreservesFiniteLimits (proEtaleModuleInverseImage i B))
      (_ : PreservesFiniteColimits (proEtaleModuleInverseImage i B))
      (_ : PreservesFiniteLimits (proEtaleModuleInverseImage U.hom B))
      (_ : PreservesFiniteColimits (proEtaleModuleInverseImage U.hom B))
      (_ : PreservesFiniteLimits (proEtaleRingedDirectImage i B))
      (_ : PreservesFiniteColimits (proEtaleRingedDirectImage i B))
      (_ : (ringedClosedKernelShriek i U.hom B aj).Additive)
      (a0 : proEtaleRingedDirectImage i B ⊣ ringedClosedKernelShriek i U.hom B aj)
      (eH : ringedSupportKernel U.hom B aj ≅
        ringedClosedKernelShriek i U.hom B aj ⋙ proEtaleRingedDirectImage i B),
      eH.hom = Functor.whiskerLeft (ringedSupportKernel U.hom B aj) ai.unit ∧
      eH.hom ≫ a0.counit = kernel.ι aj.unit ∧
      (∀ P, IsIso (ai.counit.app P)) ∧
      (∀ P, IsIso (aj.counit.app P)) ∧
      ∃ (q : proEtaleRingModules U.left
          ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj B) ≌
          SheafOfModules.{u + 1} ((proEtaleModuleCoefficients B).over U))
        (_eq : proEtaleModuleInverseImage U.hom B ⋙ q.functor ≅
          SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients B) U)
        (_ : (q.functor ⋙ proEtaleRingedExtensionByZero U B).Additive)
        (_ : PreservesFiniteLimits (q.functor ⋙ proEtaleRingedExtensionByZero U B))
        (_ : PreservesFiniteColimits (q.functor ⋙ proEtaleRingedExtensionByZero U B))
        (_aBang : q.functor ⋙ proEtaleRingedExtensionByZero U B ⊣
          proEtaleModuleInverseImage U.hom B)
        (d0 : (proEtaleRingedDirectImage i B).mapDerivedCategory ⊣
          (ringedClosedKernelShriek i U.hom B aj).rightDerivedFunctor)
        (di : (proEtaleModuleInverseImage i B).mapDerivedCategory ⊣
          (proEtaleRingedDirectImage i B).mapDerivedCategory)
        (dj : (proEtaleModuleInverseImage U.hom B).mapDerivedCategory ⊣
          (proEtaleRingedDirectImage U.hom B).rightDerivedFunctor),
        Nonempty ((q.functor ⋙ proEtaleRingedExtensionByZero U B).mapDerivedCategory ⊣
          (proEtaleModuleInverseImage U.hom B).mapDerivedCategory) ∧
        (∀ P, IsIso (di.counit.app P)) ∧
        (∀ P, IsIso (dj.counit.app P)) ∧
        (∀ P, IsZero ((proEtaleModuleInverseImage U.hom B).mapDerivedCategory.obj
          ((proEtaleRingedDirectImage i B).mapDerivedCategory.obj P))) ∧
        (∀ (I : CochainComplex (proEtaleRingModules Z
            ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj B)) ℤ),
          di.counit.app (DerivedCategory.Q.obj I) =
            (proEtaleModuleInverseImage i B).mapDerivedCategory.map
              ((proEtaleRingedDirectImage i B).mapDerivedCategoryFactors.hom.app I) ≫
            (proEtaleModuleInverseImage i B).mapDerivedCategoryFactors.hom.app
              (((proEtaleRingedDirectImage i B).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((ai.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)) ∧
        (∀ (I : CochainComplex (proEtaleRingModules U.left
            ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj B)) ℤ) [I.IsKInjective],
          dj.counit.app (DerivedCategory.Q.obj I) =
            (proEtaleModuleInverseImage U.hom B).mapDerivedCategory.map
              ((proEtaleRingedDirectImage U.hom B).rightDerivedFunctorObjQIso I).hom ≫
            (proEtaleModuleInverseImage U.hom B).mapDerivedCategoryFactors.hom.app
              (((proEtaleRingedDirectImage U.hom B).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((aj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)) ∧
        (∀ (K I : CochainComplex (proEtaleRingModules X B) ℤ)
          (r : K ⟶ I) [QuasiIso r] [I.IsKInjective],
          d0.counit.app (DerivedCategory.Q.obj K) =
            (proEtaleRingedDirectImage i B).mapDerivedCategory.map
              (ringedClosedKernelResolutionIso i U.hom B aj r).hom ≫
            (proEtaleRingedDirectImage i B).mapDerivedCategoryFactors.hom.app
              (((ringedClosedKernelShriek i U.hom B aj).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((a0.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I) ≫
            inv (DerivedCategory.Q.map r))
        := by
  classical
  have hp := proEtale_ringed_open_closed i U hU B
  let q := hp.choose
  have hq := hp.choose_spec
  let eq := hq.1.some
  let ai := hq.2.choose
  let aBang₀ := hq.2.choose_spec.choose
  have hx := hq.2.choose_spec.choose_spec
  have hci := hx.1
  have hbang := hx.2.1
  have hz := hx.2.2.1
  have hbl := hx.2.2.2.2.1
  have hbc := hx.2.2.2.2.2.1
  have hil := hx.2.2.2.2.2.2.1
  have hic := hx.2.2.2.2.2.2.2.1
  have hs := hx.2.2.2.2.2.2.2.2.1
  have hi := (proEtale_immersion_inverseImage_preservesLimits i).2.2 B
  have haddi := hi.choose
  have hli := hi.choose_spec.1
  have hci' := hi.choose_spec.2.1
  have hj := (proEtale_immersion_inverseImage_preservesLimits U.hom).2.2 B
  have haddj := hj.choose
  have hlj := hj.choose_spec.1
  have hcj := hj.choose_spec.2.1
  let aj := ringedInverseImageAdjunction U.hom B
  let er : proEtaleModuleInverseImage U.hom B ≅
      SheafOfModules.overFunctor (proEtaleModuleCoefficients B) U ⋙ q.inverse :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ q.unitIso ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eq q.inverse
  let aBang := (q.toAdjunction.comp aBang₀).ofNatIsoRight er.symm
  have : IsIso ai.counit := NatIso.isIso_of_isIso_app _
  have : IsIso aBang₀.unit := NatIso.isIso_of_isIso_app _
  have := aBang₀.fullyFaithfulLOfIsIsoUnit.full
  have := aBang₀.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso aBang.unit := inferInstance
  have : IsIso aj.counit :=
    (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨aBang, aj⟩).mp inferInstance
  have : (proEtaleRingedDirectImage i B).Additive := ai.right_adjoint_additive
  have : (proEtaleRingedDirectImage U.hom B).Additive := aj.right_adjoint_additive
  have : (q.functor ⋙ proEtaleRingedExtensionByZero U B).Additive :=
    aBang.left_adjoint_additive
  have : q.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : (SheafOfModules.overFunctor (proEtaleModuleCoefficients B) U).Additive :=
    Functor.additive_of_iso eq
  have : (proEtaleRingedExtensionByZero U B).Additive := aBang₀.left_adjoint_additive
  have hsup (N : proEtaleRingModules X B)
      (h0 : IsZero ((proEtaleModuleInverseImage U.hom B).obj N)) :
      IsIso (ai.unit.app N) :=
    supportedUnitIso ai aBang₀ (fun M ↦ ⟨(hs M).2.1, (hs M).2.2⟩) N
      ((q.functor.map_isZero h0).of_iso (eq.app N).symm)
  have hJR (P) : IsZero ((proEtaleModuleInverseImage U.hom B).obj
      ((proEtaleRingedDirectImage i B).obj P)) :=
    IsZero.of_full_of_faithful_of_isZero q.functor _ ((hz P).of_iso (eq.app _))
  -- Projections avoid transporting the large dependent goal through a case split.
  have hker := closedKernelConstruction ai aj hsup hJR
  have hadd0 := hker.choose
  let a0 := hker.choose_spec.choose
  let eH := hker.choose_spec.choose_spec.choose
  have heH := hker.choose_spec.choose_spec.choose_spec.1
  have hec := hker.choose_spec.choose_spec.choose_spec.2
  have hlb : PreservesFiniteLimits (q.functor ⋙ proEtaleRingedExtensionByZero U B) :=
    comp_preservesFiniteLimits _ _
  have hcb : PreservesFiniteColimits (q.functor ⋙ proEtaleRingedExtensionByZero U B) :=
    comp_preservesFiniteColimits _ _
  refine ⟨ai, aj, haddi, haddj, inferInstance, inferInstance, hli, hci', hlj, hcj,
    hil, hic, hadd0, a0, eH, heH, hec, hci, (fun _ ↦ inferInstance),
    q, eq, inferInstance, hlb, hcb, aBang,
    a0.mapDerivedCategoryRightDerivedAdjunction, exactDerivedAdjunction ai,
    aj.mapDerivedCategoryRightDerivedAdjunction, ⟨exactDerivedAdjunction aBang⟩,
    exactDerivedAdjunction_counit_isIso ai, rightDerivedAdjunction_counit_isIso aj,
    ?_, exactDerivedAdjunction_counit ai, rightDerivedAdjunction_counit aj, ?_⟩
  · intro P
    apply Functor.isZero_mapDerivedCategory_obj
    intro n
    exact (hJR ((DerivedCategory.homologyFunctor _ n).obj P)).of_iso
      ((proEtaleModuleInverseImage U.hom B).mapIso
        (((proEtaleRingedDirectImage i B).mapDerivedCategoryHomologyFunctorIso n).app P).symm)
  · intro K I r hr hI
    exact rightDerivedAdjunction_counit_resolution a0 r

end AlgebraicGeometry.Scheme
