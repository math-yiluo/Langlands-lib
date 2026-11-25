/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive

import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing

/-! # Realization of the locally finite coefficient ring

The isomorphisms are characterized by all finite-subextension inclusions and commute
with the actual coefficient pushforward maps. The target is the existing native
locally finite function sheaf, read in abelian sheaves through its lax monoidal
forgetful functor. An isomorphism preserving its ring-object structure is precisely
an isomorphism of ring sheaves; their ring structures are commutative.

## References

* Hemo--Richarz--Scholbach, Example 3.1 and the finite-subextension colimit preceding Lemma 5.6
* Hemo--Richarz--Scholbach, Example 3.1 and the colimit preceding Lemma 5.6
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private lemma finiteComparison_eq_chart (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (CondensedQbarCoefficientRealization.fieldDiagramIso ℓ T).hom.app E =
      chartComparison T E := by
  unfold CondensedQbarCoefficientRealization.fieldDiagramIso
  change (CondensedQbarCoefficientRealization.finiteFieldComparisonIso E ℓ T).hom.hom = _
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ _ = adj.homEquiv _ _ ((adj.homEquiv _ _).symm _)
  rw [Equiv.apply_symm_apply]
  ext S f
  exact CondensedQbarCoefficientRealization.finiteFieldComparison_test E ℓ T S.unop f.down

private lemma finiteLeg_native (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (V : T.ProEtᵒᵖ)
    (s : ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf T E)).obj.obj V) (x : V.unop.left) :
    (((((padicAlgClSheafCocone T ℓ).ι.app E ≫
      padicAlgClSheafToAdicConstantSheaf T ℓ).hom.app V) s).down.1 x) =
        (s.down x : PadicAlgCl ℓ) := by
  let J := Scheme.ProEt.topology T
  let R := padicSubfieldSheaf T ℓ E.1
  let RAb := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hu : (Sheaf.sheafifyRingPresheafIso J R).inv.hom = toSheafify J RAb.obj := by
    change (sheafToPresheaf J Ab.{u + 1}).map
      (inv ((sheafificationAdjunction J Ab.{u + 1}).counit.app RAb)) = _
    rw [Functor.map_inv]
    exact (sheafificationAdjunction J Ab.{u + 1}).inv_counit_map
  have hf : toSheafify J (padicAlgClRingPresheaf T ℓ ⋙ forget₂ RingCat Ab) ≫
      (padicAlgClSheafToAdicConstantSheaf T ℓ).hom =
        padicAlgClPresheafToAdicConstantSheaf T ℓ := by
    exact ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).apply_symm_apply _
  change (((((padicSubfieldSheafToPadicAlgClSheaf T ℓ E.1) ≫
    padicAlgClSheafToAdicConstantSheaf T ℓ).hom.app V) s).down.1 x) = _
  unfold padicSubfieldSheafToPadicAlgClSheaf continuousMapRingSheafToPadicAlgClSheaf
    Sheaf.sheafComposeToSheafify
  change ((((((Sheaf.sheafifyRingPresheafIso J R).inv.hom ≫ _) ≫
    (padicAlgClSheafToAdicConstantSheaf T ℓ).hom).app V) s).down.1 x) = _
  rw [hu, Category.assoc, ← toSheafify_naturality_assoc, hf]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma coefficient_pushforward_naturality
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Γ] (a : Λ ⟶ Γ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarFromPoint Y).map a ≫ condensedPushforwardHom Γ f =
      condensedPushforwardHom Λ f ≫
        (lowerStar Ab.{u + 1} f).map ((upperStarFromPoint X).map a) := by
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} f
  have hu := adj.unit.naturality ((upperStarFromPoint Y).map a)
  have hn := (upperStarFromPointComp f).hom.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu hn
  change (upperStarFromPoint Y).map a ≫
      adj.unit.app ((upperStarFromPoint Y).obj Γ) ≫
        (lowerStar Ab.{u + 1} f).map ((upperStarFromPointComp f).hom.app Γ) =
    (adj.unit.app ((upperStarFromPoint Y).obj Λ) ≫
      (lowerStar Ab.{u + 1} f).map ((upperStarFromPointComp f).hom.app Λ)) ≫ _
  rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
    hn, Functor.map_comp, Category.assoc]

private lemma finiteLeg_native_naturality (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ((padicAlgClSheafCocone Y ℓ).ι.app E ≫ padicAlgClSheafToAdicConstantSheaf Y ℓ) ≫
        (weilCoefficientsForgetAb ℓ Y).map (adicConstantSheafToLowerStar ℓ f) =
      CondensedRing.continuousFunctionPushforward f E ≫
        (lowerStar Ab.{u + 1} f).map
          ((padicAlgClSheafCocone X ℓ).ι.app E ≫ padicAlgClSheafToAdicConstantSheaf X ℓ) := by
  ext V s
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, lowerStar_map_hom_app']
  change (((((padicAlgClSheafCocone Y ℓ).ι.app E ≫
    padicAlgClSheafToAdicConstantSheaf Y ℓ).hom.app V) s).down.1
      ((CategoryTheory.Limits.pullback.fst V.unop.hom f) x)) = _
  rw [finiteLeg_native]
  change (s.down ((CategoryTheory.Limits.pullback.fst V.unop.hom f) x) : PadicAlgCl ℓ) =
    (((((padicAlgClSheafCocone X ℓ).ι.app E ≫
      padicAlgClSheafToAdicConstantSheaf X ℓ).hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V.unop)))
          ((CondensedRing.continuousFunctionPushforward f E).hom.app V s)).down.1 x)
  rw [finiteLeg_native, CondensedRing.continuousFunctionPushforward_app]
  rfl

/-- The finite-subextension condensed coefficient ring pulls back canonically to the
native locally finite continuous-function ring, naturally for every scheme morphism.
The section equation fixes the comparison on every finite subextension using the
actual adjoint continuous-function realization, not an arbitrary isomorphism. -/
theorem locallyFiniteCoefficientRing_realization (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ θ : ∀ T : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj ℓ) T ≅
        (weilCoefficientsForgetAb ℓ T).obj (adicConstantSheaf ℓ T),
      (∀ T : Scheme.{u}, IsMonHom (θ T).hom) ∧
      (∀ (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ)
          (V : T.ProEtᵒᵖ)
          (s : (condensedRingObj (Profinite.continuousMapRingObj E) T).obj.obj V)
          (x : V.unop.left),
        (((((upperStarFromPoint T).map
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫
              (θ T).hom).hom.app V) s).down.1 x) =
          (((chartComparison T E).hom.app V s).down x : PadicAlgCl ℓ)) ∧
      (∀ (X Y : Scheme.{u}) (h : X ⟶ Y),
        condensedPushforwardHom (Profinite.padicAlgClRingObj ℓ) h ≫
            (lowerStar Ab.{u + 1} h).map (θ X).hom =
          (θ Y).hom ≫
            (weilCoefficientsForgetAb ℓ Y).map (adicConstantSheafToLowerStar ℓ h)) := by
  let θ (T : Scheme.{u}) : condensedRingObj (Profinite.padicAlgClRingObj ℓ) T ≅
      (weilCoefficientsForgetAb ℓ T).obj (adicConstantSheaf ℓ T) :=
    (Mon.forget _).mapIso
      (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ T) ≪≫
        padicAlgClSheafIsoAdicConstantSheaf T ℓ
  have hθ (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (upperStarFromPoint T).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫
        (θ T).hom = chartComparison T E ≫
          (padicAlgClSheafCocone T ℓ).ι.app E ≫
            padicAlgClSheafToAdicConstantSheaf T ℓ := by
    change (upperStarFromPoint T).map (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫
      ((CondensedQbarCoefficientRealization.globalCoefficientIso ℓ T).hom.hom ≫
        padicAlgClSheafToAdicConstantSheaf T ℓ) = _
    rw [← Category.assoc,
      CondensedQbarCoefficientRealization.globalCoefficientIso_fac, finiteComparison_eq_chart,
      Category.assoc]
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro T
    change IsMonHom
      ((CondensedQbarCoefficientRealization.globalCoefficientIso ℓ T).hom.hom ≫
        padicAlgClSheafToAdicConstantSheaf T ℓ)
    infer_instance
  · intro T E V s x
    rw [hθ]
    change (((((padicAlgClSheafCocone T ℓ).ι.app E ≫
      padicAlgClSheafToAdicConstantSheaf T ℓ).hom.app V)
        ((chartComparison T E).hom.app V s)).down.1 x) = _
    exact finiteLeg_native ℓ T E V _ x
  · intro X Y h
    have hmon (T : Scheme.{u}) : IsMonHom (θ T).hom := by
      change IsMonHom
        ((CondensedQbarCoefficientRealization.globalCoefficientIso ℓ T).hom.hom ≫
          padicAlgClSheafToAdicConstantSheaf T ℓ)
      infer_instance
    let A := Mon.mk (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
    let B := Mon.mk ((lowerStar Ab.{u + 1} h).obj
      ((weilCoefficientsForgetAb ℓ X).obj (adicConstantSheaf ℓ X)))
    let a : A ⟶ B := Mon.Hom.mk (condensedPushforwardHom (Profinite.padicAlgClRingObj ℓ) h ≫
      (lowerStar Ab.{u + 1} h).map (θ X).hom)
    let F := lowerStar (WeilCoefficients.{u} ℓ) h
    let G := weilCoefficientsForgetAb ℓ Y
    let H := weilCoefficientsForgetAb ℓ X
    let L := lowerStar Ab.{u + 1} h
    let e : F ⋙ G ≅ H ⋙ L :=
      Functor.sheafPushforwardContinuousCompSheafComposeIso
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h)
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (forget₂ (WeilCoefficients.{u} ℓ) Ab.{u + 1})
    let R := Mon.mk (adicConstantSheaf ℓ X)
    let d : G.mapMon.obj (F.mapMon.obj R) ≅ L.mapMon.obj (H.mapMon.obj R) :=
      (Functor.mapMonCompIso (F := F) (G := G)).symm.app R ≪≫
        (Functor.mapMonNatIso e).app R ≪≫
          (Functor.mapMonCompIso (F := H) (G := L)).app R
    have hd : d.hom.hom = 𝟙 _ := by
      simp only [d, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Mon.comp_hom',
        Functor.mapMonCompIso_inv_app_hom, Functor.mapMonCompIso_hom_app_hom,
        Functor.mapMonNatIso_hom_app_hom]
      rfl
    let c : Mon.mk (adicConstantSheaf ℓ Y) ⟶ F.mapMon.obj R :=
      Mon.Hom.mk (adicConstantSheafToLowerStar ℓ h)
    let b : A ⟶ B := Mon.Hom.mk (θ Y).hom ≫ G.mapMon.map c ≫ d.hom
    suffices hab : a = b by
      have hab' := congrArg Mon.Hom.hom hab
      simpa only [a, b, c, Mon.comp_hom', Functor.mapMon_map_hom, hd,
        Category.comp_id] using hab'
    apply (completedCondensedAlgebraicClosure Y ℓ).some.hom_ext
    intro E
    apply Mon.Hom.ext
    simp only [a, b, c, Mon.comp_hom', Functor.mapMon_map_hom, hd, Category.comp_id]
    change (upperStarFromPoint Y).map
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫ _ =
        (upperStarFromPoint Y).map
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) ≫ _
    rw [← Category.assoc, coefficient_pushforward_naturality, Category.assoc,
      ← Functor.map_comp, hθ, Functor.map_comp, ← Category.assoc,
      CondensedRing.continuousChart_scheme_naturality, Category.assoc,
      ← finiteLeg_native_naturality, ← Category.assoc, ← hθ, Category.assoc]

end AlgebraicGeometry.ProEtale
