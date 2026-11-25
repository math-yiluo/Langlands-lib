/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
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
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Closed inverse image preserves limits

A sheaf of rings is a monoid object in abelian sheaves, and its module sheaves are
`CategoryTheory.Mod`. This includes noncommutative rings. The canonical inverse image
is the existing `Functor.mapMod` applied to the monoidal sheaf inverse image.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme

section Localization
universe u'
open AlgebraicGeometry MorphismProperty AlgebraicGeometry.ProEtale CategoryTheory.Category
variable (A : Type u') [Category.{u + 1} A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}

variable [WeaklyEtale j] [WeaklyEtale j']

private instance localPullbackMapContinuous :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g' ⋙
    MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j')).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
  have := Scheme.ProEt.isContinuous_overPullback g'
  have := Scheme.ProEt.isContinuous_overMap (inferInstance : @WeaklyEtale _ _ j')
  Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology U') _

private instance localMapPullbackContinuous :
    (MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j) ⋙
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g'').IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
  have := Scheme.ProEt.isContinuous_overPullback g''
  have := Scheme.ProEt.isContinuous_overMap (inferInstance : @WeaklyEtale _ _ j)
  Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology Z) _

/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` on pro-étale sheaves, with the pullbacks
along the weakly étale morphisms `j` and `j'` computed as restrictions along the localization
functors: the map induced by `CategoryTheory.MorphismProperty.Over.pullbackMapComparison`. -/
private noncomputable def localRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    (g'')_*[A] ⋙ ProEtale.localizationRestriction A j inferInstance ⟶
      ProEtale.localizationRestriction A j' inferInstance ⋙ (g')_*[A] :=
  Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') sq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')

/-- If the square is cartesian, the base change map on restrictions is an isomorphism, being
induced by an isomorphism of site functors. -/
private lemma isIso_localRestrictionBaseChangeMap_of_isPullback
    (hsq : IsPullback g' j' j g'') :
    IsIso (localRestrictionBaseChangeMap A hsq.toCommSq) :=
  have := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : @WeaklyEtale _ _ j) (inferInstance : @WeaklyEtale _ _ j') hsq
  inferInstanceAs (IsIso (Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') hsq.toCommSq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')))

private noncomputable def siteMate (sq : CommSq g' j' j g'') :=
  (mateEquiv
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j (inferInstance : WeaklyEtale j) trivial)
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j'
      (inferInstance : WeaklyEtale j') trivial)
    (TwoSquare.mk _ _ _ _ (MorphismProperty.Over.pullbackMapComparison
      (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale j') sq)))
private theorem siteMate_eq (sq : CommSq g' j' j g'') :
    siteMate sq = (MorphismProperty.Over.pullbackComp g' j).inv ≫
      (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) sq.w).hom ≫
      (MorphismProperty.Over.pullbackComp j' g'').hom := by
  ext b
  dsimp [siteMate, mateEquiv]
  set_option backward.defeqAttrib.useBackward true in
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]

private lemma isIso_mate_localRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    IsIso ((mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)))) := by
  have hs : IsIso (siteMate sq) := by rw [siteMate_eq]; infer_instance
  have h (F : Sheaf (ProEt.topology U') A) (b : Z.ProEt) :
      ((mateEquiv
        (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
        (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F).hom.app
          (op b) = F.obj.map ((siteMate sq).app b).op := by
    simp only [Functor.comp_obj, mateEquiv, ProEtale.localizationRestrictionLowerStarAdjunction,
      Adjunction.sheafPushforwardContinuous, Functor.id_obj,
      localRestrictionBaseChangeMap, Functor.sheafPushforwardContinuousNatTrans,
      ObjectProperty.ι_obj, Equiv.coe_fn_mk, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.leftUnitor_hom_app, comp_id, id_comp,
      ObjectProperty.FullSubcategory.comp_hom, Adjunction.whiskerLeft_unit_app_app,
      Functor.op_obj, Adjunction.op_unit_app, NatTrans.op_app,
      Adjunction.whiskerLeft_counit_app_app, Adjunction.op_counit_app,
      ProEtale.lowerStar_map_hom_app]
    change F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _ = _
    simp only [← Functor.map_comp]
    dsimp [siteMate, mateEquiv]
    simp only [id_comp, comp_id, ← Functor.map_comp, ← op_comp]
    simp only [Functor.map_comp, op_comp, Category.assoc]
  have hF (F : Sheaf (ProEt.topology U') A) : IsIso ((mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F) := by
    have hB : ∀ b : Z.ProEtᵒᵖ, IsIso (((mateEquiv
        (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
        (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F).hom.app b) :=
      fun b ↦ by rw [h F b.unop]; infer_instance
    apply (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ A)).mp
    change IsIso (((mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F).hom)
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

variable [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_inverseMate_localRestrictionBaseChange (sq : CommSq g' j' j g'') :
    IsIso (((mateEquiv (proEtaleSheafAdjunction g'' A)
      (proEtaleSheafAdjunction g' A)).symm
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)))) := by
  let ai := proEtaleSheafAdjunction g'' A
  let ak := proEtaleSheafAdjunction g' A
  let aj := localizationRestrictionLowerStarAdjunction A j inferInstance
  let ab := localizationRestrictionLowerStarAdjunction A j' inferInstance
  let beta := TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)
  let alpha := (mateEquiv ai ak).symm beta
  have hm : mateEquiv ai ak alpha = beta := (mateEquiv ai ak).apply_symm_apply beta
  have h := iterated_mateEquiv_conjugateEquiv ai ak aj ab alpha
  rw [hm] at h
  have hc : IsIso (conjugateEquiv (ai.comp ab) (aj.comp ak) alpha) := by
    rw [← h]
    exact isIso_mate_localRestrictionBaseChangeMap A sq
  have := hc
  let e := (conjugateIsoEquiv (ai.comp ab) (aj.comp ak)).symm
    (asIso (conjugateEquiv (ai.comp ab) (aj.comp ak) alpha))
  have he : e.hom = alpha :=
    (conjugateEquiv (ai.comp ab) (aj.comp ak)).symm_apply_apply alpha
  change IsIso alpha
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_unit_sections_of_localization
    (hsq : IsPullback g' j' j g'') (W : U.ProEt)
    (F : Sheaf (ProEt.topology Z) A)
    (hη : IsIso (((proEtaleSheafAdjunction g' A).unit.app
      ((localizationRestriction A j inferInstance).obj F)).hom.app (op W))) :
    IsIso (((proEtaleSheafAdjunction g'' A).unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) := by
  let ai := proEtaleSheafAdjunction g'' A
  let ak := proEtaleSheafAdjunction g' A
  let G := localizationRestriction A j inferInstance
  let R := proEtaleSheafDirectImage g' A
  let beta := TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A hsq.toCommSq)
  let alpha := (mateEquiv ai ak).symm beta
  have : IsIso alpha := isIso_inverseMate_localRestrictionBaseChange A hsq.toCommSq
  have : IsIso beta := isIso_localRestrictionBaseChangeMap_of_isPullback A hsq
  have hu := unit_mateEquiv_symm ai ak beta F
  have hu' := congrArg (fun f ↦ f.hom.app (op W)) hu
  change ((ai.unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
      (beta.app _).hom.app (op W) =
    (ak.unit.app (G.obj F)).hom.app (op W) ≫
      (R.map (alpha.app F)).hom.app (op W) at hu'
  have : IsIso ((ak.unit.app (G.obj F)).hom.app (op W)) := hη
  have : IsIso (((ai.unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
      (beta.app _).hom.app (op W)) := by
    rw [hu']
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((beta.app _).hom.app (op W))

end Localization

end AlgebraicGeometry.Scheme
