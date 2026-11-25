/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModels
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import WeilConjectures.Algebra.Homology.SmoothPurity.ConstantLocalModuleHomSupplement
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleUnitSupplement
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalModuleIsoSupplement
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact

/-! # Finitely presented local constant models on the pro-etale site

## References

* Stacks Project, Tags 09AJ and 093U
* Stacks Project, Tag 093U (3)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Finitely presented constant local models satisfy the local weak Serre clauses. -/
theorem proEtale_fp_localModels_serre (X : Scheme.{u}) (R : Type u)
    [CommRing R] [IsNoetherianRing R] :
    (∀ (F G : proEtaleRingModules X (proEtaleConstantRing X R)) (f : F ⟶ G),
      IsFinitelyPresentedLocallyConstantProEtaleModule F →
      IsFinitelyPresentedLocallyConstantProEtaleModule G →
      IsFinitelyPresentedLocallyConstantProEtaleModule (kernel f) ∧
        IsFinitelyPresentedLocallyConstantProEtaleModule (cokernel f)) ∧
    (∀ S : ShortComplex (proEtaleRingModules X (proEtaleConstantRing X R)),
      S.ShortExact → IsFinitelyPresentedLocallyConstantProEtaleModule S.X₁ →
      IsFinitelyPresentedLocallyConstantProEtaleModule S.X₃ →
      IsFinitelyPresentedLocallyConstantProEtaleModule S.X₂) := by
  let : IsNoetherianRing (ULift.{u + 1, u} R) :=
    isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
  let E := proEtaleFPModelEncoding X R
  have : E.functor.IsEquivalence := E.isEquivalence_functor
  have h := SheafOfModules.finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions
    (proEtaleModelTopology X) (ULift.{u + 1, u} R)
  have trans {F G : ringedSiteModules.{u + 1}
      ((constantSheaf (proEtaleModelTopology X) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} R)))} (e : F ≅ G)
      (hF : SheafOfModules.IsFiniteTypeLocallyConstant (proEtaleModelTopology X)
        (ULift.{u + 1, u} R) F) :
      SheafOfModules.IsFiniteTypeLocallyConstant (proEtaleModelTopology X)
        (ULift.{u + 1, u} R) G := by
    intro V
    obtain ⟨T, hT, ht⟩ := hF V
    refine ⟨T, hT, fun W f hf ↦ ?_⟩
    obtain ⟨M, hM, ⟨i⟩⟩ := ht W f hf
    exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ W).mapIso e.symm ≪≫ i⟩⟩
  constructor
  · intro F G f hF hG
    obtain ⟨hK, hC⟩ := h.1 _ _ (E.functor.map f)
      ((proEtale_fp_localModels_comparison X R F).mp hF)
      ((proEtale_fp_localModels_comparison X R G).mp hG)
    exact ⟨(proEtale_fp_localModels_comparison X R _).mpr
        (trans (PreservesKernel.iso E.functor f).symm hK),
      (proEtale_fp_localModels_comparison X R _).mpr
        (trans (PreservesCokernel.iso E.functor f).symm hC)⟩
  · intro S hS h₁ h₃
    apply (proEtale_fp_localModels_comparison X R _).mpr
    exact h.2 (S.map E.functor) (hS.map_of_exact E.functor)
      ((proEtale_fp_localModels_comparison X R _).mp h₁)
      ((proEtale_fp_localModels_comparison X R _).mp h₃)

end AlgebraicGeometry.Scheme
