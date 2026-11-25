/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
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
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
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
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all Mathlib.Data.Matrix.Basic
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Inverse image of continuous coefficient rings

## References

* Bhatt--Scholze, Section 6.8
* Bhatt--Scholze, Section 6.8, continuous coefficients
* Stacks Tag 03D2
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj

namespace LatticePullbackProof

open ContinuousRingUniverse CondensedRing

private noncomputable def latticeAdditiveDirectMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (latticeCoefficientSheaf X T) ⟶
    (lowerStar Ab.{u + 1} f).obj ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (latticeCoefficientSheaf Y T)) :=
  ⟨Functor.whiskerRight (continuousCoefficientDirectImageMap f T).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})⟩

private noncomputable def additiveDirectMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousCoefficientRingSheaf X T) ⟶
    (lowerStar Ab.{u + 1} f).obj ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf Y T)) :=
  ⟨{ app := fun V ↦ AddCommGrpCat.ofHom
       { toFun := fun s ↦ ULift.up (s.down.comp (pullback.fst V.unop.hom f).base.hom)
         map_zero' := rfl
         map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro V W g
       apply ConcreteCategory.hom_ext
       intro s
       apply ULift.ext
       ext x
       change s.down ((pullback.fst W.unop.hom f ≫ g.unop.left).base x) =
         s.down ((((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map g.unop).left ≫
           pullback.fst V.unop.hom f).base x)
       rw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
       rfl }⟩

private noncomputable def coefficientAbIso (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousCoefficientRingSheaf X T) ≅
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (latticeCoefficientSheaf X T) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

private lemma additiveDirectMap_square {X Y : Scheme.{u}} (f : Y ⟶ X)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    additiveDirectMap f T ≫ (lowerStar Ab.{u + 1} f).map (coefficientAbIso Y T).hom =
      (coefficientAbIso X T).hom ≫ latticeAdditiveDirectMap f T := by
  ext V s
  rfl

private lemma comparison_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type u) [TopologicalSpace O] [CommRing O] [IsTopologicalRing O] :
    condensedPushforwardHom (Profinite.continuousMapRingObjOfUniverse O) f ≫
      (lowerStar Ab.{u + 1} f).map (ContinuousRingUniverse.comparison Y O) =
    ContinuousRingUniverse.comparison X O ≫ additiveDirectMap f O := by
  let adjX := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  let CY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf Y O)
  have hleft := chartMate_homEquiv f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f)
    (pointUpperStar.obj (Profinite.continuousMapRingObjOfUniverse O)) CY
      (ContinuousRingUniverse.comparison Y O)
  rw [← condensedPullbackHom_eq (Profinite.continuousMapRingObjOfUniverse O) f] at hleft
  apply (adjX.homEquiv _ _).injective
  conv_rhs => rw [adjX.homEquiv_naturality_right]
  have hchart : adjX.homEquiv _ _ (ContinuousRingUniverse.comparison X O) =
      ContinuousRingUniverse.comparisonAdjoint X O := by
    unfold ContinuousRingUniverse.comparison
    exact Equiv.apply_symm_apply _ _
  rw [hchart]
  simp only [adjX, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  simp only [← unitAlgHom_comp_map_condensedPullbackHom, Category.assoc]
  erw [hleft, pointUpperStarLowerStarAdjunction.homEquiv_naturality_right]
  have hchartY :
      (pointUpperStarLowerStarAdjunction.comp
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y))).homEquiv _ _
          (ContinuousRingUniverse.comparison Y O) =
            ContinuousRingUniverse.comparisonAdjoint Y O := by
    unfold ContinuousRingUniverse.comparison
    exact Equiv.apply_symm_apply _ _
  simp only [Adjunction.comp_homEquiv] at hchartY
  erw [hchartY]
  ext S s
  apply ULift.ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  change ((((lowerStarFactor Ab.{u + 1} (comp_toSpecZ f)).inv.app CY).hom.app
    (op (profiniteToProEt.obj S.unop)))
      (ULift.up (s.down.comp (profiniteTestProjection Y S.unop)))).down =
    (((additiveDirectMap f O).hom.app
      (op ((profiniteToProEtOf X).obj S.unop)))
        (ULift.up (s.down.comp (profiniteTestProjection X S.unop)))).down
  rw [lowerStarFactor_inv_app_hom_app]
  change (s.down.comp (profiniteTestProjection Y S.unop)).comp
      (((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left.base.hom) =
    (s.down.comp (profiniteTestProjection X S.unop)).comp
      (pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f).base.hom
  have hp :
      ((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ Y) =
      pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f ≫
        pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ X) := by
    simp only [MorphismProperty.Over.pullbackComp_inv_app_left]
    dsimp only [pullback.map]
    erw [Category.assoc, pullback.lift_fst]
    simp only [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    rfl
  have hp' := congrArg (fun g ↦ g.base.hom) hp
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hp'
  simp only [profiniteTestProjection, ContinuousMap.comp_assoc]
  rw [hp']

private theorem additiveInverseMap_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] :
    IsIso (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
      (latticeAdditiveDirectMap f T)) := by
  let a := upperStarLowerStarAdjunction Ab.{u + 1} f
  let b := (a.homEquiv _ _).symm (latticeAdditiveDirectMap f T)
  let cX := ContinuousRingUniverse.comparison X T ≫ (coefficientAbIso X T).hom
  let cY := ContinuousRingUniverse.comparison Y T ≫ (coefficientAbIso Y T).hom
  let Λ := Profinite.continuousMapRingObjOfUniverse T
  let := ContinuousRingUniverse.comparison_isIso X T
  let := ContinuousRingUniverse.comparison_isIso Y T
  have hn : condensedPushforwardHom Λ f ≫ (lowerStar Ab.{u + 1} f).map cY =
      cX ≫ latticeAdditiveDirectMap f T := by
    dsimp only [cX, cY]
    rw [Functor.map_comp, ← Category.assoc, comparison_naturality]
    rw [Category.assoc, additiveDirectMap_square, ← Category.assoc]
  have he : (upperStar Ab.{u + 1} f).map cX ≫ b =
      condensedPullbackHom Λ f ≫ cY := by
    apply (a.homEquiv _ _).injective
    rw [a.homEquiv_naturality_left]
    dsimp only [b]
    erw [Equiv.apply_symm_apply]
    rw [a.homEquiv_naturality_right]
    exact hn.symm
  have : IsIso ((upperStar Ab.{u + 1} f).map cX ≫ b) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left ((upperStar Ab.{u + 1} f).map cX) b

private theorem ringAdjunct_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (h : R ⟶ (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S)
    (hb : IsIso (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).symm
      (show (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R ⟶
        (lowerStar Ab.{u + 1} f).obj ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S) from
        ⟨Functor.whiskerRight h.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})⟩))) :
    IsIso (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm h) := by
  let F := Scheme.proEtaleBaseChange f
  let J := Scheme.ProEt.topology X
  let K := Scheme.ProEt.topology Y
  let : Limits.PreservesFiniteLimits F := inferInstance
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let : (CategoryTheory.forget CommRingCat.{u + 1}).PreservesLeftKanExtensions F.op := by
    intro P
    let : Limits.PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget CommRingCat.{u + 1}) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        (CategoryTheory.forget CommRingCat.{u + 1}) P F.op V := by
      intro V
      infer_instance
    infer_instance
  let : (CategoryTheory.forget Ab.{u + 1}).PreservesLeftKanExtensions F.op := by
    intro P
    let : Limits.PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget Ab.{u + 1}) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        (CategoryTheory.forget Ab.{u + 1}) P F.op V := by
      intro V
      infer_instance
    infer_instance
  let e := sheafPullbackForgetIso J K F (CategoryTheory.forget CommRingCat.{u + 1})
  let a := sheafPullbackForgetIso J K F (CategoryTheory.forget Ab.{u + 1})
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let B := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S
  let hA : A ⟶ (lowerStar Ab.{u + 1} f).obj B :=
    ⟨Functor.whiskerRight h.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})⟩
  let b := ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv A B).symm hA
  let := hb
  let UR := sheafCompose K (CategoryTheory.forget CommRingCat.{u + 1})
  let UA := sheafCompose K (CategoryTheory.forget Ab.{u + 1})
  let ea := a.app A
  let er := e.app R
  have hr := sheafPullbackForgetIso_unit J K F
    (CategoryTheory.forget CommRingCat.{u + 1}) R
  have ha := sheafPullbackForgetIso_unit J K F
    (CategoryTheory.forget Ab.{u + 1}) A
  have heq : er.hom ≫ ea.inv ≫ UA.map b =
      UR.map (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm h) := by
    apply (cancel_epi er.inv).1
    simp only [er.inv_hom_id_assoc]
    apply ((sheafAdjunctionContinuous F (Type (u + 1)) J K).homEquiv _ _).injective
    have hr' : (sheafAdjunctionContinuous F (Type (u + 1)) J K).unit.app
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R) ≫
        (F.sheafPushforwardContinuous (Type (u + 1)) J K).map er.inv =
      (sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).map
        ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R) := by
      rw [← hr]
      change _ ≫ (F.sheafPushforwardContinuous (Type (u + 1)) J K).map er.hom ≫
        (F.sheafPushforwardContinuous (Type (u + 1)) J K).map er.inv = _
      simp only [← Functor.map_comp, er.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.comp_id]
      rfl
    have ha' : (sheafAdjunctionContinuous F (Type (u + 1)) J K).unit.app
        ((sheafCompose J (CategoryTheory.forget Ab.{u + 1})).obj A) ≫
        (F.sheafPushforwardContinuous (Type (u + 1)) J K).map ea.inv =
      (sheafCompose J (CategoryTheory.forget Ab.{u + 1})).map
        ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app A) := by
      rw [← ha]
      change _ ≫ (F.sheafPushforwardContinuous (Type (u + 1)) J K).map ea.hom ≫
        (F.sheafPushforwardContinuous (Type (u + 1)) J K).map ea.inv = _
      simp only [← Functor.map_comp, ea.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.comp_id]
      rfl
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    erw [ha', hr']
    have hb := ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv A B).apply_symm_apply hA
    have hc := Equiv.apply_symm_apply
      ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _) h
    have hab := congrArg (sheafCompose J (CategoryTheory.forget Ab.{u + 1})).map hb
    have hcr := congrArg (sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).map hc
    exact hab.trans hcr.symm
  have : IsIso (UR.map
      (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm h)) := by
    rw [← heq]
    infer_instance
  exact isIso_of_reflects_iso
    (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm h) UR

/-- The canonical coefficient adjunct is invertible for totally disconnected rings. -/
theorem continuousCoefficientInverseImageMap_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] : IsIso (continuousCoefficientInverseImageMap f T) := by
  exact ringAdjunct_isIso f (latticeCoefficientSheaf X T) (latticeCoefficientSheaf Y T)
    (continuousCoefficientDirectImageMap f T) (additiveInverseMap_isIso f T)

end LatticePullbackProof
end AlgebraicGeometry.ProEtale
