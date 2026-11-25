/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionDerivedTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTotalComparison
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
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSliceDerivedHomComparison
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceNormalizedComparisons
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTensorLocalization
import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison

/-! # Internal-module and ringed-site derived Hom

## Main statements

* `moduleObject_ringedSite_derived_comparison`: naturality, evaluation and slices.

## References

* Stacks 06YS
* Stacks 06YL
* Stacks Project, Tags 08J9, 08JA, 08JB
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule WeilConjectures

-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

universe u₀ v₀ u₁

section ClosedTransport
set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [Category A] [Category B]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}

private theorem uncurryClosed (S : CoefficientClosedStructure H) (P K N : A)
    (f : P ⟶ H.obj (op K, N)) :
    (S.transpose P K N).symm f =
      S.tensor.map (f, 𝟙 K) ≫ S.evaluation K N := by
  change (@MonoidalCategory.tensorRight A _ S.monoidal K).map f ≫ _ = _
  let _ := S.monoidal
  simp [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation]

private theorem closedScalarUncurry
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    {F : A ⥤ B} {G : B ⥤ A} (ad : F ⊣ G)
    (t : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)
    (K N : A) (M : B) (k : N ⟶ G.obj M) :
    (T.transpose _ (F.obj K) M).symm
        ((ad.homEquiv _ _).symm
          (H.map (Prod.mkHom (𝟙 (op K)) k) ≫ (ClosedScalarHom.component S T ad t K M).inv)) =
      t.inv.app (H.obj (op K, N), K) ≫ F.map (S.evaluation K N) ≫
        (ad.homEquiv N M).symm k := by
  let b := H.map (Prod.mkHom (𝟙 (op K)) k) ≫ (ClosedScalarHom.component S T ad t K M).inv
  have hb := ClosedScalarHom.component_rep S T ad t (H.obj (op K, N)) K M b
  dsimp only [b] at hb
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hb
  have hc := congrArg (S.transpose _ K (G.obj M)).symm hb
  dsimp only [ClosedScalarHom.bijection, Equiv.trans_apply, Iso.homCongr,
    Equiv.coe_fn_mk, Iso.symm_inv, Iso.refl_hom] at hc
  erw [Equiv.symm_apply_apply, Category.comp_id] at hc
  erw [uncurryClosed S] at hc
  have hnat : S.tensor.map (H.map (Prod.mkHom (𝟙 (op K)) k), 𝟙 K) ≫
      S.evaluation K (G.obj M) = S.evaluation K N ≫ k := by
    simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
      Prod.sectR] using (S.adjunction K).counit.naturality k
  rw [hnat] at hc
  have hd := congrArg (ad.homEquiv _ M).symm hc
  erw [Equiv.symm_apply_apply, ad.homEquiv_naturality_left_symm] at hd
  apply (cancel_epi (t.hom.app (H.obj (op K, N), K))).mp
  change t.hom.app (H.obj (op K, N), K) ≫ _ = _ at hd
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ad.homEquiv_naturality_left_symm] using hd

private def closedEquivalenceIso
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    (E : A ≌ B) (t : S.tensor ⋙ E.functor ≅ (E.functor.prod E.functor) ⋙ T.tensor) :
    H ⋙ E.functor ≅ (E.functor.op.prod E.functor) ⋙ I := by
  let ηH : H ≅ ((𝟭 Aᵒᵖ).prod (E.functor ⋙ E.inverse)) ⋙ H :=
    NatIso.ofComponents
      (fun p ↦ H.mapIso ((Iso.refl p.1).prod (E.unitIso.app p.2))) (by
        intro p q f
        simp only [Functor.comp_map, Functor.prod_map, Functor.id_map,
          Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
        rw [← H.map_comp, ← H.map_comp]
        congr 1
        ext
        · simp
        · exact E.unitIso.hom.naturality f.2)
  let σ : H ≅ (E.functor.op.prod E.functor) ⋙ I ⋙ E.inverse :=
    ηH ≪≫ Functor.isoWhiskerLeft ((𝟭 Aᵒᵖ).prod E.functor)
      (ClosedScalarHom.iso S T E.toAdjunction t).symm
  exact Functor.isoWhiskerRight σ E.functor ≪≫
    Functor.isoWhiskerLeft ((E.functor.op.prod E.functor) ⋙ I) E.counitIso

private theorem closedEquivalenceEvaluation
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    (E : A ≌ B) (t : S.tensor ⋙ E.functor ≅ (E.functor.prod E.functor) ⋙ T.tensor)
    (K N : A) :
    E.functor.map (S.evaluation K N) =
      t.hom.app (H.obj (op K, N), K) ≫
        T.tensor.map (Prod.mkHom
          ((closedEquivalenceIso S T E t).hom.app (op K, N)) (𝟙 (E.functor.obj K))) ≫
        T.evaluation (E.functor.obj K) (E.functor.obj N) := by
  have h := closedScalarUncurry S T E.toAdjunction t K N
    (E.functor.obj N) (E.unitIso.hom.app N)
  have hu : (E.toAdjunction.homEquiv N (E.functor.obj N)).symm
      (E.unitIso.hom.app N) = 𝟙 _ := by
    exact E.toAdjunction.homEquiv_symm_unit N
  rw [hu, Category.comp_id] at h
  change (T.transpose _ (E.functor.obj K) (E.functor.obj N)).symm
    ((closedEquivalenceIso S T E t).hom.app (op K, N)) = _ at h
  rw [uncurryClosed] at h
  rw [h, Iso.hom_inv_id_app_assoc]

end ClosedTransport

section RestrictionTransport
set_option backward.isDefEq.respectTransparency false

universe a₂ b₂ a₃ b₃
variable {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{a₂} D]
  {E : Type b₂} [Category.{a₃} E] {F : Type b₃} [Category F]

private theorem restrictionLift
    (h : Cᵒᵖ × C ⥤ C) (hu : Eᵒᵖ × E ⥤ E)
    (H : Dᵒᵖ × D ⥤ D) (HU : Fᵒᵖ × F ⥤ F)
    (e : C ⥤ D) (eu : E ⥤ F) [eu.Full] [eu.Faithful]
    (r : C ⥤ E) (rs : D ⥤ F) (c : r ⋙ eu ≅ e ⋙ rs)
    (theta : h ⋙ e ≅ (e.op.prod e) ⋙ H)
    (thetaU : hu ⋙ eu ≅ (eu.op.prod eu) ⋙ HU)
    (rho : H ⋙ rs ≅ (rs.op.prod rs) ⋙ HU) :
    ∃ z : h ⋙ r ≅ (r.op.prod r) ⋙ hu,
      AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.homRestrictionSquare
        h hu H HU e eu r rs (fun K ↦ c.app K) theta thetaU
        (fun K N ↦ rho.app (op K, N)) z := by
  let cH : ((r ⋙ eu).op.prod (r ⋙ eu)) ⋙ HU ≅
      ((e ⋙ rs).op.prod (e ⋙ rs)) ⋙ HU :=
    Functor.isoWhiskerRight (NatIso.prod (NatIso.op c.symm) c) HU
  let z : (h ⋙ r) ⋙ eu ≅ ((r.op.prod r) ⋙ hu) ⋙ eu :=
    Functor.isoWhiskerLeft h c ≪≫ Functor.isoWhiskerRight theta rs ≪≫
      Functor.isoWhiskerLeft (e.op.prod e) rho ≪≫ cH.symm ≪≫
      Functor.isoWhiskerLeft (r.op.prod r) thetaU.symm
  refine ⟨Functor.fullyFaithfulCancelRight eu z, ?_⟩
  intro K N
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  change ((c.app (h.obj (op K, N))).hom ≫
    rs.map (theta.hom.app (op K, N)) ≫ rho.hom.app (op (e.obj K), e.obj N) ≫
      cH.inv.app (op K, N) ≫ thetaU.inv.app (op (r.obj K), r.obj N)) ≫
    thetaU.hom.app (op (r.obj K), r.obj N) ≫ cH.hom.app (op K, N) = _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  change (c.app (h.obj (op K, N))).hom ≫ rs.map (theta.hom.app (op K, N)) ≫
    rho.hom.app (op (e.obj K), e.obj N) ≫ 𝟙 _ =
    (c.app (h.obj (op K, N))).hom ≫ rs.map (theta.hom.app (op K, N)) ≫
      rho.hom.app (op (e.obj K), e.obj N)
  rw [Category.comp_id]

end RestrictionTransport

section NativeClosed
set_option backward.isDefEq.respectTransparency false

variable (A : Type*) [Category A] [MonoidalCategory A] [BraidedCategory A]

private def reverseSwap (K : A) : tensorLeft K ≅ tensorRight K :=
  NatIso.ofComponents (fun P ↦ (β_ P K).symm)
    (fun f ↦ BraidedCategory.braiding_inv_naturality_right K f)

private def nativeClosed (H : Aᵒᵖ ⥤ A ⥤ A) (ad : curriedTensor A ⊣₂ H) :
    CoefficientClosedStructure (Functor.uncurry.obj H) where
  monoidal := inferInstance
  adjunction K := ((ad.adj K).ofNatIsoLeft (reverseSwap A K)).ofNatIsoRight
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro P Q f
      change (H.obj (op K)).map f ≫ 𝟙 _ = 𝟙 _ ≫
        (H.map (𝟙 (op K))).app P ≫ (H.obj (op K)).map f
      rw [Category.comp_id, Category.id_comp, CategoryTheory.Functor.map_id,
        NatTrans.id_app, Category.id_comp]))
  evaluation_naturality := by
    intro K K' N f
    have hc := congr_app (ad.whiskerLeft_map_counit f) N
    change f ▷ (H.obj (op K)).obj N ≫ (ad.adj K).counit.app N =
      K' ◁ (H.map f.op).app N ≫ (ad.adj K').counit.app N at hc
    have h : (H.map f.op).app N ▷ K' ≫
        (β_ ((H.obj (op K')).obj N) K').hom ≫ (ad.adj K').counit.app N =
      (H.obj (op K)).obj N ◁ f ≫
        (β_ ((H.obj (op K)).obj N) K).hom ≫ (ad.adj K).counit.app N := by
      rw [BraidedCategory.braiding_naturality_left_assoc, ← hc,
        ← BraidedCategory.braiding_naturality_right_assoc]
    simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatIso.ofComponents_inv_app, Iso.refl_inv, reverseSwap, Iso.symm_inv,
      Functor.uncurry_obj_map, Functor.uncurry_obj_obj,
      CategoryTheory.Functor.map_id, Category.comp_id,
      tensorRight, tensorLeft, curriedTensor, Functor.flip]
    change (H.map f.op).app N ▷ K' ≫
        𝟙 ((H.obj (op K')).obj N) ▷ K' ≫
          (β_ ((H.obj (op K')).obj N) K').hom ≫ (ad.adj K').counit.app N =
      (H.obj (op K)).obj N ◁ f ≫ 𝟙 ((H.obj (op K)).obj N) ▷ K ≫
        (β_ ((H.obj (op K)).obj N) K).hom ≫ (ad.adj K).counit.app N
    simpa only [MonoidalCategory.id_whiskerRight, Category.id_comp] using h

private theorem nativeClosed_evaluation (H : Aᵒᵖ ⥤ A ⥤ A)
    (ad : curriedTensor A ⊣₂ H) (K N : A) :
    (nativeClosed A H ad).evaluation K N =
      (β_ ((H.obj (op K)).obj N) K).hom ≫ (ad.adj K).counit.app N := by
  simp only [CoefficientClosedStructure.evaluation, nativeClosed,
    Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatIso.ofComponents_inv_app, Iso.refl_inv, reverseSwap, Iso.symm_inv,
    tensorRight, curriedTensor, Functor.flip]
  change 𝟙 ((H.obj (op K)).obj N) ▷ K ≫
    (β_ ((H.obj (op K)).obj N) K).hom ≫ (ad.adj K).counit.app N = _
  rw [MonoidalCategory.id_whiskerRight, Category.id_comp]

private def uncurryTensorIso :
    Functor.uncurry.obj (curriedTensor A) ≅ MonoidalCategory.tensor A :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro p q f
    simp only [Functor.uncurry_obj_map, curriedTensor, MonoidalCategory.tensor_map,
      Iso.refl_hom, Category.comp_id, Category.id_comp, MonoidalCategory.tensorHom_def])

private theorem nativeClosedEquivalence
    (H : Aᵒᵖ ⥤ A ⥤ A) (ad : curriedTensor A ⊣₂ H)
    {B : Type*} [Category B] {I : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure I) (E : A ≌ B)
    (t : Functor.uncurry.obj (curriedTensor A) ⋙ E.functor ≅
      (E.functor.prod E.functor) ⋙ S.tensor) :
    ∃ θ : Functor.uncurry.obj H ⋙ E.functor ≅ (E.functor.op.prod E.functor) ⋙ I,
      ∀ K N : A,
        E.functor.map ((β_ ((H.obj (op K)).obj N) K).hom ≫
          (ad.adj K).counit.app N) =
        t.hom.app ((H.obj (op K)).obj N, K) ≫
          S.tensor.map
            (X := (E.functor.obj ((H.obj (op K)).obj N), E.functor.obj K))
            (Y := (I.obj (op (E.functor.obj K), E.functor.obj N), E.functor.obj K))
            (θ.hom.app (op K, N), 𝟙 (E.functor.obj K)) ≫
          S.evaluation (E.functor.obj K) (E.functor.obj N) := by
  let t' : (nativeClosed A H ad).tensor ⋙ E.functor ≅
      (E.functor.prod E.functor) ⋙ S.tensor :=
    Functor.isoWhiskerRight (uncurryTensorIso A).symm E.functor ≪≫ t
  refine ⟨closedEquivalenceIso (nativeClosed A H ad) S E t', ?_⟩
  intro K N
  have h := closedEquivalenceEvaluation (nativeClosed A H ad) S E t' K N
  rw [nativeClosed_evaluation] at h
  have ht' (K N : A) : t'.hom.app (K, N) = t.hom.app (K, N) := by
    change E.functor.map (𝟙 _) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [ht'] at h
  convert h using 1 <;> rfl

private theorem nativeClosedEquivalenceTensor
    (H : Aᵒᵖ ⥤ A ⥤ A) (ad : curriedTensor A ⊣₂ H)
    {B : Type*} [Category B] {I : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure I) (E : A ≌ B)
    (t : MonoidalCategory.tensor A ⋙ E.functor ≅
      (E.functor.prod E.functor) ⋙ S.tensor) :
    ∃ θ : Functor.uncurry.obj H ⋙ E.functor ≅ (E.functor.op.prod E.functor) ⋙ I,
      ∀ K N : A,
        E.functor.map ((β_ ((H.obj (op K)).obj N) K).hom ≫
          (ad.adj K).counit.app N) =
        t.hom.app ((H.obj (op K)).obj N, K) ≫
          S.tensor.map
            (X := (E.functor.obj ((H.obj (op K)).obj N), E.functor.obj K))
            (Y := (I.obj (op (E.functor.obj K), E.functor.obj N), E.functor.obj K))
            (θ.hom.app (op K, N), 𝟙 (E.functor.obj K)) ≫
          S.evaluation (E.functor.obj K) (E.functor.obj N) := by
  let t' := Functor.isoWhiskerRight (uncurryTensorIso A) E.functor ≪≫ t
  obtain ⟨θ, hθ⟩ := nativeClosedEquivalence A H ad S E t'
  have ht' (K N : A) : t'.hom.app (K, N) = t.hom.app (K, N) := by
    change E.functor.map (𝟙 _) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  refine ⟨θ, ?_⟩
  intro K N
  rw [← ht']
  exact hθ K N

end NativeClosed

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

private theorem globalNativeMonoidal_eq_localization
    (C : Type u₀) [Category.{v₀} C] [Abelian C] [IsGrothendieckAbelian.{v₀} C]
    [HasDerivedCategory.{v₀} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C]
    [(DerivedCategory.Qh (C := C)).HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (.up ℤ))] :
    DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory C =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (.up ℤ)) := by
  rfl

/-- The native derived tensor uses the K-flat localization monoidal structure. -/
theorem internalMonoidal_eq_localization :
    (inferInstance : MonoidalCategory (DerivedCategory (Internal Λ X))) =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Internal Λ X) (.up ℤ)) := by
  exact globalNativeMonoidal_eq_localization (Internal Λ X)

/-- The actual derived Koszul braiding, transported along the preceding equality. -/
instance internalBraiding : BraidedCategory (DerivedCategory (Internal Λ X)) :=
  Eq.mp (congrArg (fun m ↦ @BraidedCategory (DerivedCategory (Internal Λ X)) _ m)
    (internalMonoidal_eq_localization Λ X).symm)
    (DerivedMonoidal.braidedCategory' DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Internal Λ X) (.up ℤ)))

attribute [local irreducible] sectionModuleEquivalence CondensedRing.derivedHom
  sliceEquivalence sliceDerivedClosed CondensedRing.derivedTensorHomAdjunction₂
  Mod.derivedMonoidalCategory DerivedCategory.monoidalClosed
  MonoidalClosed.internalHom MonoidalClosed.internalHomAdjunction₂

private theorem globalHom
    (S : CoefficientClosedStructure (hom Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring Λ X) S)
    (t : TensorComparison Λ X S T) :
    ∃ θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
        ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X,
      ∀ K N : DerivedCategory (Internal Λ X),
        (forward Λ X).map
          ((@BraidedCategory.braiding _ _ _ (internalBraiding Λ X)
              (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) K).hom ≫
            (CondensedRing.derivedTensorHomAdjunction Λ K).counit.app N) =
          t.iso.hom.app (((CondensedRing.derivedHom Λ X).obj (op K)).obj N, K) ≫
            S.tensor.map
              (X := ((forward Λ X).obj (((CondensedRing.derivedHom Λ X).obj (op K)).obj N),
                (forward Λ X).obj K))
              (Y := ((hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N),
                (forward Λ X).obj K))
              (θ.hom.app (op K, N), 𝟙 ((forward Λ X).obj K)) ≫
              S.evaluation ((forward Λ X).obj K) ((forward Λ X).obj N) := by
  let _ : MonoidalCategory (DerivedCategory (Internal Λ X)) := Mod.derivedMonoidalCategory
  let _ := internalBraiding Λ X
  have : (forward Λ X).IsEquivalence := by
    unfold forward
    infer_instance
  exact nativeClosedEquivalence (DerivedCategory (Internal Λ X))
    (CondensedRing.derivedHom Λ X) (CondensedRing.derivedTensorHomAdjunction₂ Λ X) S
    (forward Λ X).asEquivalence t.iso

private theorem sliceHomIso
    (U : X.ProEt)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU)
    (tU : SliceTensorComparison Λ X U SU TU) :
    ∃ θU : sliceNativeHom Λ X U ⋙ sliceDerivedForward Λ X U ≅
      ((sliceDerivedForward Λ X U).op.prod (sliceDerivedForward Λ X U)) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
          ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U),
      sliceHomEvaluationNormalized Λ X U SU TU tU θU := by
  let _ : MonoidalCategory (DerivedCategory (SliceInternal Λ X U)) :=
    sliceDerivedMonoidal Λ X U
  let _ : MonoidalClosed (DerivedCategory (SliceInternal Λ X U)) :=
    sliceDerivedClosed Λ X U
  let _ := sliceBraiding Λ X U
  obtain ⟨θU, hθU⟩ := nativeClosedEquivalenceTensor
    (DerivedCategory (SliceInternal Λ X U)) MonoidalClosed.internalHom
    MonoidalClosed.internalHomAdjunction₂ SU (sliceDerivedEquivalence Λ X U) tU.iso
  refine ⟨θU, ?_⟩
  intro K N
  dsimp only [sliceNativeEvaluation, sliceNativeHom]
  exact hθU K N

private theorem sliceHom
    (U : X.ProEt) (S : CoefficientClosedStructure (hom Λ X))
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU)
    (tU : SliceTensorComparison Λ X U SU TU)
    (d : RingedSliceEvaluationComparisons (hom Λ X)
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
      (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) U) S SU
      (RingedSliceFlatRestriction.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring Λ X) U))
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X) :
    Nonempty (SliceHomComparison Λ X U S SU TU tU d θ) := by
  obtain ⟨θU, hθU⟩ := sliceHomIso Λ X U SU TU tU
  let E := sliceDerivedEquivalence Λ X U
  let rs := ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
    (Scheme.ProEt.topology X) (ring Λ X) U
  let ρ : hom Λ X ⋙ rs ≅ (rs.op.prod rs) ⋙
      derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) :=
    NatIso.ofComponents (fun p ↦ d.eta p.1.unop p.2) (by
      intro p q f
      exact d.eta_naturality _ _ _ _ f.1.unop f.2)
  let c : sliceInternalRestriction Λ X U ⋙ sliceDerivedForward Λ X U ≅ forward Λ X ⋙ rs :=
    Functor.isoWhiskerLeft (forward Λ X ⋙ rs) E.counitIso
  let _ : (sliceDerivedForward Λ X U).Full :=
    inferInstanceAs (sliceDerivedEquivalence Λ X U).functor.Full
  let _ : (sliceDerivedForward Λ X U).Faithful :=
    inferInstanceAs (sliceDerivedEquivalence Λ X U).functor.Faithful
  obtain ⟨z, hz⟩ := restrictionLift
    (Functor.uncurry.obj (CondensedRing.derivedHom Λ X)) (sliceNativeHom Λ X U)
    (hom Λ X) _ (forward Λ X) (sliceDerivedForward Λ X U)
    (sliceInternalRestriction Λ X U) rs c θ θU ρ
  exact ⟨⟨θU, hθU, z, hz⟩⟩

/-- Comparison of the module-object right adjoint with the K-injective sheaf-Hom
model, including its evaluation and all localized-site comparisons. -/
theorem moduleObject_ringedSite_derived_comparison :
    ∃ (S : CoefficientClosedStructure (hom Λ X))
      (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) S)
      (t : TensorComparison Λ X S T)
      (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
        ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X),
      (∀ K N : DerivedCategory (Internal Λ X),
        (forward Λ X).map
          ((@BraidedCategory.braiding _ _ _ (internalBraiding Λ X)
              (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) K).hom ≫
            (CondensedRing.derivedTensorHomAdjunction Λ K).counit.app N) =
          (t.iso.hom.app (((CondensedRing.derivedHom Λ X).obj (op K)).obj N, K)) ≫
            S.tensor.map
              (X := ((forward Λ X).obj (((CondensedRing.derivedHom Λ X).obj (op K)).obj N),
                (forward Λ X).obj K))
              (Y := ((hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N),
                (forward Λ X).obj K))
              (θ.hom.app (op K, N), 𝟙 ((forward Λ X).obj K)) ≫
            S.evaluation ((forward Λ X).obj K) ((forward Λ X).obj N)) ∧
      (∀ U : X.ProEt,
        ∃ (SU : CoefficientClosedStructure
            (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
              ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
          (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
            ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU)
          (tU : SliceTensorComparison Λ X U SU TU)
          (d : RingedSliceEvaluationComparisons (hom Λ X)
            (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
              ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
            (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
              (Scheme.ProEt.topology X) (ring Λ X) U) S SU
            (RingedSliceFlatRestriction.{u + 1, u, u}
              (Scheme.ProEt.topology X) (ring Λ X) U)),
          RingedSliceEvaluationNormalized.{u + 1, u, u, u + 1, u + 1}
            (Scheme.ProEt.topology X) (ring Λ X) U S T SU TU d ∧
          Nonempty (SliceHomComparison Λ X U S SU TU tU d θ)) := by
  obtain ⟨⟨S, T, ⟨t⟩⟩, hslice⟩ := internalSection_tensorLocalization Λ X
  obtain ⟨θ, hθ⟩ := globalHom Λ X S T t
  refine ⟨S, T, t, θ, hθ, ?_⟩
  intro U
  obtain ⟨SU, TU, ⟨tU⟩⟩ := hslice U
  obtain ⟨d, hd⟩ := (ringedSlice_normalizedComparisons.{u + 1, u, u, u + 1, u + 1}
    (Scheme.ProEt.topology X) (ring Λ X) U S T SU TU).some
  exact ⟨SU, TU, tU, d, hd, sliceHom Λ X U S SU TU tU d θ⟩

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
