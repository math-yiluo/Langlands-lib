/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
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
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# The presheaf description of bounded-below higher direct images

Source: Stacks Project, Tag 0D6I, lemma-unbounded-describe-higher-direct-images,
and the first paragraph of the blueprint corollary-continuity-cohomology--2
(blueprint: lem-pe-bounded-complex-direct-image-presheaf).

All coefficient sheaves, complexes, presheaves and conclusions use the original
small pro-etale sites. The AsSmall model is used only to construct resolutions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Sectionwise additivity of transport back to the original site.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
instance ringModuleFromModel_additive {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (proEtaleModuleFromModel R).Additive := ⟨by intros; rfl⟩

/-- The sectionwise identity identifies round-trip transport with the original modules.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleModelRoundTrip {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    𝟭 (ringedSiteModules.{u + 1} R) ≅
      proEtaleModuleToModel R ⋙ proEtaleModuleFromModel R :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _)))

/-- The model replacement used by the landed ringHypercohomology, before transport back.
Source: Stacks Tag 079P (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleModelResolutionFunctor {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    CochainComplex.kInjectiveResolutionFunctor.{u + 1} (ringedSiteModules.{u + 1} S)

/-- One functorial resolution on the original site, transported from the small model.
Source: Stacks Tags 079P and 03D1
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleResolutionFunctor {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    CochainComplex (ringedSiteModules.{u + 1} R) ℤ ⥤
      CochainComplex (ringedSiteModules.{u + 1} R) ℤ :=
  ringModuleModelResolutionFunctor R ⋙
    (proEtaleModuleFromModel R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The actual augmentation of the transported functorial resolution.
Source: Stacks Tags 079P and 03D1
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleResolutionMap {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1})
    (K : CochainComplex (ringedSiteModules.{u + 1} R) ℤ) :
    K ⟶ (ringModuleResolutionFunctor R).obj K :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  let A := (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ)
  let B := (proEtaleModuleFromModel R).mapHomologicalComplex (ComplexShape.up ℤ)
  let s : A.obj K ⟶ (CochainComplex.kInjectiveResolutionFunctor.{u + 1}
      (ringedSiteModules.{u + 1} S)).obj (A.obj K) :=
    (CochainComplex.toKInjectiveResolution.{u + 1} (ringedSiteModules.{u + 1} S)).app
      (A.obj K)
  ((Functor.mapHomologicalComplexIdIso (ringedSiteModules.{u + 1} R)
      (ComplexShape.up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (ringModuleModelRoundTrip R) (ComplexShape.up ℤ)).hom.app K ≫
    B.map s

/-- The specified transported complex and augmentation form a K-injective resolution.
Source: Stacks Tags 079P, 03D1 and 0D6I
(blueprint: lem-pe-bounded-complex-direct-image-presheaf).
Proof: the sectionwise transports to and from AsSmall are inverse additive equivalences.
They preserve acyclic complexes, chain homotopies and quasi-isomorphisms. The model
module category is Grothendieck, so its published functorial replacement is K-injective
and its augmentation a quasi-isomorphism. Transporting its Hom vanishing against every
acyclic complex proves K-injectivity back on the original site. The transported
augmentation is exactly ringModuleResolutionMap, since the round-trip on sections is
the identity. Thus both assertions hold without any resolution-existence hypothesis. -/
theorem ringModuleResolution_isKInjective_quasiIso {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1})
    (K : CochainComplex (ringedSiteModules.{u + 1} R) ℤ) :
    ((ringModuleResolutionFunctor R).obj K).IsKInjective ∧
      QuasiIso (ringModuleResolutionMap R K) := by
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  let := SheafOfModules.isGrothendieckAbelian S
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology X) (topology X) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology X) (topology X)
    infer_instance
  let e : SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 R) (𝟙 S)
      (by ext U; dsimp [AsSmall.equiv]; erw [S.obj.map_id]; rfl)
      (by ext U; dsimp [AsSmall.equiv]; erw [R.obj.map_id]; rfl)
  let : (proEtaleModuleFromModel R).IsEquivalence :=
    inferInstanceAs e.functor.IsEquivalence
  constructor
  · change CochainComplex.IsKInjective
      (((proEtaleModuleFromModel R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.kInjectiveResolutionFunctor.{u + 1}
          (ringedSiteModules.{u + 1} S)).obj
            (((proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
    infer_instance
  · let A := (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ)
    let B := (proEtaleModuleFromModel R).mapHomologicalComplex (ComplexShape.up ℤ)
    let s := (CochainComplex.toKInjectiveResolution.{u + 1}
      (ringedSiteModules.{u + 1} S)).app (A.obj K)
    have : QuasiIso s := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1}
      (ringedSiteModules.{u + 1} S) (A.obj K)).2
    have : QuasiIso (B.map s) := inferInstance
    change QuasiIso (_ ≫ B.map s)
    exact quasiIso_comp _ (B.map s)

/-- Evaluation on the model, forgetting only the sectionwise module action.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleModelEvaluation {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  SheafOfModules.evaluation S (op (AsSmall.up.obj U)) ⋙
    forget₂ (ModuleCat.{u + 1} (S.obj.obj (op (AsSmall.up.obj U)))) AddCommGrpCat.{u + 1}

/-- Sectionwise evaluation is additive.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
instance ringModuleModelEvaluation_additive {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) :
    (ringModuleModelEvaluation R U).Additive := ⟨by intros; rfl⟩

end AlgebraicGeometry.Scheme.ProEt
