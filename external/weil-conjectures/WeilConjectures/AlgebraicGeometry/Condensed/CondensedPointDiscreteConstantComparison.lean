/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement

/-!
# Discrete constant coefficients on the geometric point

Source: main-20261015, coefficient lemma, second paragraph.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] Sheaf.monoidalCategory

private theorem constantRingMonObj {C : Type*} [Category C] (B : Type*) [Ring B] :
    (Functor.const C).monObjObj (AddCommGrpCat.of B) =
      Functor.monObjCompForget₂ ((Functor.const C).obj (RingCat.of B)) := by
  apply MonObj.ext
  ext U
  rfl

private theorem constantSheafRingMonObj {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal] (B : Type (u + 1)) [Ring B] :
    (constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of B) =
      Sheaf.monObj_presheafToSheaf_obj J
        (((Functor.const Cᵒᵖ).obj (RingCat.of B)) ⋙ forget₂ RingCat Ab) := by
  have h := Functor.monObjObj_comp (Functor.const Cᵒᵖ) (presheafToSheaf J Ab.{u + 1})
    (AddCommGrpCat.of B)
  refine h.trans ?_
  let transfer (m : MonObj ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B))) :
      MonObj ((constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of B)) :=
    @Functor.monObjObj _ _ _ _ _ _ (presheafToSheaf J Ab.{u + 1}) _ _ m
  exact congrArg transfer (constantRingMonObj (C := Cᵒᵖ) B)

private theorem constantRingIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J RingCat.{u + 1}]
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    [J.HasSheafCompose (forget₂ RingCat.{u + 1} Ab.{u + 1})]
    [J.PreservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1})]
    (B : Type (u + 1)) [Ring B] :
    Nonempty ((constantSheaf J Ab.{u + 1}).mapMon.obj (Mon.mk (AddCommGrpCat.of B)) ≅
      Mon.mk ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((constantSheaf J RingCat.{u + 1}).obj (RingCat.of B)))) := by
  let P := (Functor.const Cᵒᵖ).obj (RingCat.of B)
  let S := (constantSheaf J RingCat.{u + 1}).obj (RingCat.of B)
  let φ := Functor.whiskerRight (toSheafify J P) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have hφ : J.W (A := Ab.{u + 1}) φ :=
    J.W_of_preservesSheafification (forget₂ RingCat.{u + 1} Ab.{u + 1}) _
      (J.W_toSheafify P)
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff φ).mp hφ
  let e := asIso ((presheafToSheaf J Ab.{u + 1}).map φ) ≪≫
    Sheaf.sheafifyRingPresheafIso J S
  have he : IsMonHom e.hom := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    infer_instance
  have h := constantSheafRingMonObj J B
  have he' : @IsMonHom _ _ _ _ _
      ((constantSheaf J Ab.{u + 1}).monObjObj (AddCommGrpCat.of B)) _ e.hom := by
    rw [h]
    exact he
  exact ⟨Mon.mkIso e he'.one_hom he'.mul_hom⟩

private noncomputable def constantToContinuous (A : Type u) [Ring A]
    [TopologicalSpace A] [DiscreteTopology A] :
    (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶
      Profinite.continuousCoefficientRingPresheaf A where
  app S := RingCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

end AlgebraicGeometry.ProEtale
