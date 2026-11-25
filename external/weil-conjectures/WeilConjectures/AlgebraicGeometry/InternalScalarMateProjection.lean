/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
import WeilConjectures.AlgebraicGeometry.InternalScalarRestrictionMateNormalization
import WeilConjectures.AlgebraicGeometry.InternalScalarTensorPullNormalization
import WeilConjectures.AlgebraicGeometry.ModuleRingedToposDerivedComparison
import all WeilConjectures.AlgebraicGeometry.SectionDerivedTensorNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalTensorCounit

/-! # Restricting the internal scalar mate gives the specified projection map

(1), (3);
Stacks Project, Tags 07A4, 0D6E, 0B56 and 0944
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

set_option allowUnsafeReducibility true

attribute [local reducible] L F CondensedRing.moduleObjectDerivedPullback
  CondensedRing.moduleObjectDerivedPushforward

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

/-- The canonical restriction/pullback comparison, obtained from the ordinary identified
coefficient comparison by exact localization and the specified derived counits.
Source: Stacks 0D6D, 07A6 (auxiliary; not a blueprint node). -/
def scalarRestrictionPull (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L Λ' f ⋙ V a X ≅ V a Y ⋙ L Λ f := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' f) (V a X) ≪≫
    CondensedRing.derivedComapUpperStarIso a f ≪≫
    Functor.isoWhiskerLeft (V a Y)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm

/-- The canonical restriction/direct-image arrow is the geometric right mate of the
inverse restriction/pullback comparison. The node asserts its invertibility, as supplied
by the adjunction-compatible ringed-topos restriction comparison.
Source: Stacks 0D6E, 07A6 (auxiliary; not a blueprint node). -/
def scalarRestrictionPush (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    F Λ' f ⋙ V a Y ⟶ V a X ⋙ F Λ f :=
  (mateEquiv (adj Λ' f) (adj Λ f)
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPull a f).inv))

/-- Restriction of the regular coefficient in degree zero, with the exact localization
and single-complex comparisons retained.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def scalarCoefficientUnit (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (V a T).obj (𝟙_ (DerivedCategory (Modules Λ' T))) ≅ B a T :=
  cast (by rfl) <| (V₀ a T).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (Modules Λ' T) 0).obj
        (Mod.regular (condensedRingObj Λ' T))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (V₀ a T) (.up ℤ) 0).app
        (Mod.regular (condensedRingObj Λ' T)))

/-- The cartesian coefficient pullback: restrict the canonical regular-module unit
comparison, after the identified-coefficient restriction/pullback comparison.
Source: Stacks 07A4; blueprint coefficient morphisms alpha_f
(auxiliary; not a blueprint node). -/
def scalarCoefficientPull (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (L Λ f).obj (B a Y) ≅ B a X :=
  (L Λ f).mapIso (scalarCoefficientUnit a Y).symm ≪≫
    (scalarRestrictionPull a f).symm.app (𝟙_ (DerivedCategory (Modules Λ' Y))) ≪≫
    (V a X).mapIso (by
      unfold L CondensedRing.moduleObjectDerivedPullback
      exact CondensedRing.leftDerivedUpperStarUnitIso Λ' f) ≪≫
    scalarCoefficientUnit a X

/-- The specified internal tensor comparison with the scalar interface's functor name.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarTensorPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (Modules Λ Y)) :
    (L Λ f).obj (M ⊗ N) ⟶ (L Λ f).obj M ⊗ (L Λ f).obj N :=
  ((CondensedRing.leftDerivedUpperStarTensor Λ f).app M).app N

/-- The specified module-object projection arrow, followed by the cartesian coefficient
identification. The first factor is literally the published moduleObjectProjectionMap,
and the second factor is its specified postcomposition under the derived direct image;
no new tensor comparison or adjunction is chosen.
Source: Stacks 0B56 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarProjection (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategory (Modules Λ X)) :
    ((CondensedRing.derivedTensor Λ Y).obj ((F Λ f).obj K)).obj (B a Y) ⟶
      (F Λ f).obj (((CondensedRing.derivedTensor Λ X).obj K).obj (B a X)) :=
  CondensedRing.moduleObjectProjectionMap Λ f K (B a Y) ≫
    (F Λ f).map (((CondensedRing.derivedTensor Λ X).obj K).map
      (scalarCoefficientPull a f).hom)

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]

/-- The cartesian coefficient identification in the fixed section derived category.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def scalarSectionCoefficientPull (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ModuleRingedComparison.derivedPullback Λ f).obj
        ((ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj (B a Y)) ≅
      (ModuleRingedComparison.derivedEquivalence Λ X).functor.obj (B a X) :=
  (scalarSectionPullComparison Λ f).symm.app (B a Y) ≪≫
    (ModuleRingedComparison.derivedEquivalence Λ X).functor.mapIso (scalarCoefficientPull a f)

/-- The specified ringed projection: the actual ringed adjunction transpose of the
canonical ringed tensor comparison followed by counit tensor the coefficient map.
Source: Stacks 0B56, 07A4 (auxiliary; not a blueprint node). -/
def scalarSectionProjection (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.tensor Λ Y).obj
        ((ModuleRingedComparison.derivedPushforward Λ f).obj
          ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K),
          (ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj (B a Y)) ⟶
      (ModuleRingedComparison.derivedPushforward Λ f).obj
        ((ModuleRingedComparison.tensor Λ X).obj
          ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K,
            (ModuleRingedComparison.derivedEquivalence Λ X).functor.obj (B a X))) :=
  (ModuleRingedComparison.derivedAdjunction Λ f).homEquiv _ _
    ((ModuleRingedComparison.tensorPullComparison Λ f).hom.app
        ((ModuleRingedComparison.derivedPushforward Λ f).obj
          ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K),
          (ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj (B a Y)) ≫
      (ModuleRingedComparison.tensor Λ X).map (Prod.mkHom
        ((ModuleRingedComparison.derivedAdjunction Λ f).counit.app
          ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K))
        (scalarSectionCoefficientPull a f).hom))

/-- Tensor comparison with explicit scalar-interface endpoints, from the fixed equivalence.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
@[irreducible] def scalarSectionTensor (T : Scheme.{u}) (K N : DerivedCategory (Modules Λ T)) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.obj
      (((CondensedRing.derivedTensor Λ T).obj K).obj N) ≅
      (ModuleRingedComparison.tensor Λ T).obj
        ((ModuleRingedComparison.derivedEquivalence Λ T).functor.obj K,
          (ModuleRingedComparison.derivedEquivalence Λ T).functor.obj N) :=
  (ModuleRingedComparison.tensorComparison Λ T).app (K, N)

/-- The equation after the fixed section equivalence, with its tensor comparison explicit.
Source: Stacks 0B56 and 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarSectionLeft (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (_tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (K : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj
      ((V a Y).obj ((D a Y).obj ((F Λ f).obj K))) ⟶
    (ModuleRingedComparison.derivedPushforward Λ f).obj
      ((ModuleRingedComparison.tensor Λ X).obj
        ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K,
          (ModuleRingedComparison.derivedEquivalence Λ X).functor.obj (B a X))) :=
  (ModuleRingedComparison.derivedEquivalence Λ Y).functor.map
        ((V a Y).map ((rho a f lam).app K) ≫
          (scalarRestrictionPush a f).app ((D a X).obj K) ≫
          (F Λ f).map (tX.derived.hom.app K)) ≫
        (scalarSectionPushComparison Λ f).hom.app
          (((CondensedRing.derivedTensor Λ X).obj K).obj (B a X)) ≫
        (ModuleRingedComparison.derivedPushforward Λ f).map
          (scalarSectionTensor X K (B a X)).hom

/-- The right side of the section equation.
Source: Stacks 0B56 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarSectionRight (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (_lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (K : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj
      ((V a Y).obj ((D a Y).obj ((F Λ f).obj K))) ⟶
    (ModuleRingedComparison.derivedPushforward Λ f).obj
      ((ModuleRingedComparison.tensor Λ X).obj
        ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K,
          (ModuleRingedComparison.derivedEquivalence Λ X).functor.obj (B a X))) :=
  (ModuleRingedComparison.derivedEquivalence Λ Y).functor.map
          (tY.derived.hom.app ((F Λ f).obj K)) ≫
        (scalarSectionTensor Y ((F Λ f).obj K) (B a Y)).hom ≫
        (ModuleRingedComparison.tensor Λ Y).map (Prod.mkHom
          ((scalarSectionPushComparison Λ f).hom.app K) (𝟙 _)) ≫
        scalarSectionProjection a f K

/-- The normalized section equation.
Source: Stacks 0B56 (auxiliary; not a blueprint node). -/
def ScalarMateSectionEquation (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) : Prop :=
  ∀ K : DerivedCategory (Modules Λ X),
    scalarSectionLeft a f tX tY lam K = scalarSectionRight a f tX tY lam K

/-- The pullback normalization equation, with the canonical coefficient identification.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarPullLeft (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (_tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (M : DerivedCategory (Modules Λ Y)) :
    (L Λ f).obj ((V a Y).obj ((D a Y).obj M)) ⟶
      ((L Λ f).obj M ⊗ B a X) :=
  (scalarRestrictionPull a f).inv.app ((D a Y).obj M) ≫
          (V a X).map (lam.hom.app M) ≫ tX.derived.hom.app ((L Λ f).obj M)

/-- The tensor-pullback side of the first equation.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def scalarPullRight (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (_lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (M : DerivedCategory (Modules Λ Y)) :
    (L Λ f).obj ((V a Y).obj ((D a Y).obj M)) ⟶
      ((L Λ f).obj M ⊗ B a X) :=
  (L Λ f).map (tY.derived.hom.app M) ≫ scalarTensorPull f M (B a Y) ≫
          ((L Λ f).obj M ◁ (scalarCoefficientPull a f).hom)

/-- The normalized pullback equation.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
def ScalarMatePullEquation (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) : Prop :=
  ∀ M : DerivedCategory (Modules Λ Y),
    scalarPullLeft a f tX tY lam M = scalarPullRight a f tX tY lam M

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

attribute [local reducible] TwoSquare Functor.asEquivalence
  CondensedRing.moduleObjectProjectionData
  CondensedRing.moduleObjectProjectionMap CondensedRing.derivedTensor
  ModuleRingedComparison.derivedEquivalence ModuleRingedComparison.derivedFunctor
  ModuleRingedComparison.internalDerivedPullback ModuleRingedComparison.internalDerivedPushforward
  ModuleRingedComparison.comparisonSource scalarRestrictionPull scalarCoefficientPull
  scalarCoefficientUnit scalarPullLeft scalarPullRight scalarTensorPull scalarSectionTensor adj

private theorem restricted_mate_adjunct
    {C E C' E' : Type*} [Category C] [Category E] [Category C'] [Category E']
    {l : C ⥤ E} {r : E ⥤ C} (ar : l ⊣ r)
    {l' : C' ⥤ E'} {r' : E' ⥤ C'} (ar' : l' ⊣ r')
    {dC : C ⥤ C'} {dE : E ⥤ E'} {vC : C' ⥤ C} {vE : E' ⥤ E}
    (b : l' ⋙ vE ≅ vC ⋙ l) (lam : dC ⋙ l' ⟶ l ⋙ dE)
    {t : E ⥤ E} (e : dE ⋙ vE ⟶ t) (K : E) :
    l.map (vC.map ((mateEquiv ar ar' (TwoSquare.mk _ _ _ _ lam)).app K) ≫
        (mateEquiv ar' ar (TwoSquare.mk _ _ _ _ b.inv)).app (dE.obj K) ≫
        r.map (e.app K)) ≫ ar.counit.app (t.obj K) =
      b.inv.app (dC.obj (r.obj K)) ≫ vE.map (lam.app (r.obj K)) ≫
        e.app (l.obj (r.obj K)) ≫ t.map (ar.counit.app K) := by
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  have hn := ar.counit.naturality (e.app K)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  have hm := mateEquiv_counit ar' ar (TwoSquare.mk _ _ _ _ b.inv) (dE.obj K)
  slice_lhs 2 3 => exact hm
  have hb := b.inv.naturality
    ((mateEquiv ar ar' (TwoSquare.mk _ _ _ _ lam)).app K)
  dsimp only [TwoSquare.mk, Functor.comp_obj,
    Functor.comp_map] at hb
  simp only [Category.assoc]
  erw [reassoc_of% hb]
  slice_lhs 2 3 =>
    rw [← vE.map_comp]
    exact congrArg vE.map (mateEquiv_counit ar ar'
      (TwoSquare.mk _ _ _ _ lam) K)
  simp only [Functor.map_comp, Category.assoc]
  have he := e.naturality (ar.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he
  rw [he]

private theorem modified_projection_adjunct
    {C E : Type*} [Category C] [Category E]
    {l : C ⥤ E} {r : E ⥤ C} (ar : l ⊣ r)
    (tc : E ⥤ E ⥤ E) (td : C ⥤ C ⥤ C)
    (delta : (Functor.postcompose₂.obj l).obj td ⟶
      (((Functor.whiskeringLeft₂ E).obj l).obj l).obj tc)
    (K : E) (B : C) {B' : E} (c : l.obj B ⟶ B') :
    l.map (((ar.rightAdjointProjectionMap delta).app K).app B ≫
        r.map ((tc.obj K).map c)) ≫ ar.counit.app _ =
      (delta.app (r.obj K)).app B ≫
        (tc.map (ar.counit.app K)).app (l.obj B) ≫ (tc.obj K).map c := by
  rw [Functor.map_comp]
  have hn := ar.counit.naturality ((tc.obj K).map c)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [Category.assoc, hn]
  rw [← Category.assoc]
  have hp := ar.map_rightAdjointProjectionMap_app_app_comp_counit delta K B
  dsimp only [Functor.whiskeringLeft₂, Functor.whiskeringLeft,
    Functor.whiskeringRight, Functor.id_obj, Functor.comp_obj] at hp
  rw [hp]
  simp only [Category.assoc]

omit [IsCommMonObj Λ] [IsCommMonObj Λ']
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)] in
private theorem restriction_reflects (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (V a T).ReflectsIsomorphisms := by
  have h₀ : (V₀ a T).ReflectsIsomorphisms := by
    refine ⟨fun g _ ↦ ?_⟩
    have : IsIso ((Mod.forget (condensedRingObj Λ' T)).map g) := by
      change IsIso ((Mod.forget (condensedRingObj Λ T)).map ((V₀ a T).map g))
      infer_instance
    exact isIso_of_reflects_iso g (Mod.forget (condensedRingObj Λ' T))
  change (V₀ a T).mapDerivedCategory.ReflectsIsomorphisms
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((V₀ a T).map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff ((V₀ a T).mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  let := h₀
  exact isIso_of_reflects_iso _ (V₀ a T)

private theorem scalar_push_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (scalarSectionPushComparison Λ f).hom =
      (by
        unfold F CondensedRing.moduleObjectDerivedPushforward
        exact (ModuleRingedComparison.derivedPushComparison Λ f).hom) := by
  change (mateEquiv (adj Λ f) (ModuleRingedComparison.derivedAdjunction Λ f)
    (TwoSquare.mk _ _ _ _ (scalarSectionPullComparison Λ f).inv)) = _
  exact scalarSectionPushMate_eq Λ f

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)] in
private theorem scalar_internal_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules Λ X)) (N : DerivedCategory (Modules Λ Y)) :
    CondensedRing.moduleObjectProjectionMap Λ f K N =
      ModuleRingedComparison.internalProjection Λ f K N := by
  change ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _) _ = _
  unfold ModuleRingedComparison.internalProjection
  congr 2
  have hd := ModuleRingedComparison.internalDelta_eq_canonical Λ f
  rw [← CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison] at hd
  exact congrArg (fun d ↦ (d.app ((F Λ f).obj K)).app N) hd.symm

private theorem section_projection_coefficient (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategory (Modules Λ X)) :
    ModuleRingedComparison.projection Λ f
        ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K)
        ((ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj (B a Y)) ≫
      (ModuleRingedComparison.derivedPushforward Λ f).map
        ((ModuleRingedComparison.tensor Λ X).map (Prod.mkHom (𝟙 _)
          (scalarSectionCoefficientPull a f).hom)) =
      scalarSectionProjection a f K := by
  unfold ModuleRingedComparison.projection derivedProjectionFormulaMate
  rw [Adjunction.rightAdjointProjectionMap_app_app]
  change (ModuleRingedComparison.derivedAdjunction Λ f).homEquiv _ _ _ ≫
    (ModuleRingedComparison.derivedPushforward Λ f).map _ = _
  rw [← Adjunction.homEquiv_naturality_right]
  unfold scalarSectionProjection
  congr 1
  simp only [Functor.curry_map_app_app, NatTrans.comp_app,
    Functor.curryObjProdComp_hom_app_app, Functor.curry_obj_map_app,
    Category.assoc]
  rw [← Functor.map_comp]
  congr 1
  simp only [prod_comp, Category.id_comp]
  erw [Category.id_comp]
  apply congrArg (ModuleRingedComparison.tensor Λ X).map
  apply Prod.hom_ext
  · exact Category.comp_id _
  · rfl

attribute [local irreducible] ModuleRingedComparison.derivedFunctor
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.derivedPullback ModuleRingedComparison.derivedPushforward

private theorem projection_section_transport (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategory (Modules Λ X)) :
    (ModuleRingedComparison.derivedEquivalence Λ Y).functor.map (scalarProjection a f K) ≫
        (scalarSectionPushComparison Λ f).hom.app
          (((CondensedRing.derivedTensor Λ X).obj K).obj (B a X)) ≫
        (ModuleRingedComparison.derivedPushforward Λ f).map
          (scalarSectionTensor X K (B a X)).hom =
      (scalarSectionTensor Y ((F Λ f).obj K) (B a Y)).hom ≫
        (ModuleRingedComparison.tensor Λ Y).map
          (Prod.mkHom ((scalarSectionPushComparison Λ f).hom.app K) (𝟙 _)) ≫
        scalarSectionProjection a f K := by
  have hbase := ModuleRingedComparison.projection_comparison Λ f K (B a Y)
  rw [← scalar_internal_projection f K (B a Y)] at hbase
  have hbase' :
      (ModuleRingedComparison.derivedEquivalence Λ Y).functor.map
          (CondensedRing.moduleObjectProjectionMap Λ f K (B a Y)) ≫
        (scalarSectionPushComparison Λ f).hom.app
          (((CondensedRing.derivedTensor Λ X).obj K).obj ((L Λ f).obj (B a Y))) ≫
        (ModuleRingedComparison.derivedPushforward Λ f).map
          (scalarSectionTensor X K ((L Λ f).obj (B a Y))).hom ≫
        (ModuleRingedComparison.derivedPushforward Λ f).map
          ((ModuleRingedComparison.tensor Λ X).map (Prod.mkHom (𝟙 _)
            ((scalarSectionPullComparison Λ f).hom.app (B a Y)))) =
      (scalarSectionTensor Y ((F Λ f).obj K) (B a Y)).hom ≫
        (ModuleRingedComparison.tensor Λ Y).map
          (Prod.mkHom ((scalarSectionPushComparison Λ f).hom.app K) (𝟙 _)) ≫
        ModuleRingedComparison.projection Λ f
          ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K)
          ((ModuleRingedComparison.derivedEquivalence Λ Y).functor.obj (B a Y)) := by
    simpa only [scalarSectionTensor, scalar_push_hom, scalarSectionPullComparison,
      id_eq, Iso.app_hom] using hbase
  have hn := (scalarSectionPushComparison Λ f).hom.naturality
    (((CondensedRing.derivedTensor Λ X).obj K).map (scalarCoefficientPull a f).hom)
  simp only [Functor.comp_map] at hn
  have ht := (ModuleRingedComparison.tensorComparison Λ X).hom.naturality
    (Prod.mkHom (𝟙 K) (scalarCoefficientPull a f).hom)
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map] at ht
  rw [(CondensedRing.derivedTensor Λ X).map_id] at ht
  simp only [NatTrans.id_app, Category.id_comp] at ht
  rw [(ModuleRingedComparison.derivedEquivalence Λ X).functor.map_id] at ht
  change (ModuleRingedComparison.derivedEquivalence Λ X).functor.map
      (((CondensedRing.derivedTensor Λ X).obj K).map (scalarCoefficientPull a f).hom) ≫
      (scalarSectionTensor X K (B a X)).hom =
    (scalarSectionTensor X K ((L Λ f).obj (B a Y))).hom ≫
      (ModuleRingedComparison.tensor Λ X).map (Prod.mkHom (𝟙 _)
        ((ModuleRingedComparison.derivedEquivalence Λ X).functor.map
          (scalarCoefficientPull a f).hom)) at ht
  unfold scalarProjection
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ ((ModuleRingedComparison.derivedPushforward Λ f).map _), hn]
  rw [Category.assoc]
  have htm := congrArg (ModuleRingedComparison.derivedPushforward Λ f).map ht
  simp only [Functor.map_comp] at htm
  rw [htm]
  have hb := congrArg (fun z ↦ z ≫
    (ModuleRingedComparison.derivedPushforward Λ f).map
      ((ModuleRingedComparison.tensor Λ X).map (Prod.mkHom (𝟙 _)
        (scalarSectionCoefficientPull a f).hom))) hbase'
  simp only [Category.assoc] at hb
  have hc := section_projection_coefficient a f K
  conv_rhs at hb =>
    enter [2, 2]
    exact hc
  have hcoef :
      (ModuleRingedComparison.tensor Λ X).map (Prod.mkHom
        (𝟙 ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K))
        ((ModuleRingedComparison.derivedEquivalence Λ X).functor.map
          (scalarCoefficientPull a f).hom)) =
      (ModuleRingedComparison.tensor Λ X).map (Prod.mkHom
        (𝟙 ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K))
        ((scalarSectionPullComparison Λ f).hom.app (B a Y))) ≫
      (ModuleRingedComparison.tensor Λ X).map (Prod.mkHom
        (𝟙 ((ModuleRingedComparison.derivedEquivalence Λ X).functor.obj K))
        (scalarSectionCoefficientPull a f).hom) := by
    rw [← Functor.map_comp]
    apply congrArg (ModuleRingedComparison.tensor Λ X).map
    apply Prod.hom_ext
    · simp
    · unfold scalarSectionCoefficientPull
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
        prod_comp, Iso.hom_inv_id_app_assoc]
  have hcm := congrArg (ModuleRingedComparison.derivedPushforward Λ f).map hcoef
  simp only [Functor.map_comp] at hcm
  apply Eq.trans ?_ hb
  exact congrArg (fun z ↦
    (ModuleRingedComparison.derivedEquivalence Λ Y).functor.map
        (CondensedRing.moduleObjectProjectionMap Λ f K (B a Y)) ≫
      (scalarSectionPushComparison Λ f).hom.app
        (((CondensedRing.derivedTensor Λ X).obj K).obj ((L Λ f).obj (B a Y))) ≫
      (ModuleRingedComparison.derivedPushforward Λ f).map
        (scalarSectionTensor X K ((L Λ f).obj (B a Y))).hom ≫ z) hcm

/-- Restricting the normalized scalar mate gives exactly the canonical projection map,
and the fixed section equivalence gives the same equation for the ringed operations.

(1), (3);
Stacks Project, Tags 07A4, 0D6E, 0B56 and 0944
(auxiliary; not a blueprint node).

Proof, following the seven steps of the node:
1. Pass through the fixed internal/section equivalences. The normalization theorem
identifies the geometric adjunctions and scalar maps, including counits. Choose flat-term
K-flat resolutions P of M and Q of the coefficient in degree zero. Exact geometric
pullback preserves these resolutions by lem-weil-pbc-ringed-pullback-preserves-kflat.
2. The canonical tensor comparison is the signed total of the ordinary balancing map.
Augment Q to the coefficient. Tensoring with P preserves that quasi-isomorphism by
lem-pur-kflat-tensor-quasiiso-independent, before and after pullback. Thus the comparison
can be computed using the degree-zero coefficient, without asserting its K-flatness.
3. The two maps in the first equation send f inverse (p tensor s) to
f inverse p tensor c(f inverse s). The balanced universal property, followed by
sheafification, identifies them degreewise. The scalar has degree zero, so there is no
sign. Localize and cancel the resolution isomorphisms to obtain the equation for all M.
4. The ring-sheaf-change-adjunction theorem identifies the canonical restriction/push
comparison with the geometric mate of the inverse restriction/pullback comparison.
The adjunct of the restricted rho, after e_X, is therefore counit tensor identity
composed with the first equation, by naturality of e_X at the counit.
5. Substitute the first equation, interchange counit and the coefficient map using
tensor bifunctoriality, and recognize the specified projection adjunct. Injectivity of
the adjunction hom equivalence gives the second equation.
6. The section equivalences preserve ordinary tensor, signed totals and K-flat
representatives. Their fixed tensor and geometric comparisons therefore identify delta
with the representative-characterized ringed delta and identify the actual counits.
Taking the ringed adjunction transpose gives scalarSectionProjection and the third equation.
7. Counit naturality and naturality of all comparisons give the displayed naturality
and naturality of rho. Restriction reflects derived isomorphisms by the ring-sheaf-change
adjunction theorem; all other conjugating maps are isomorphisms. Thus rho is invertible
exactly when the specified projection is. No projection formula is assumed in this proof.
-/
theorem internal_scalar_mate_projection (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hX : TensorNormalized a X tX) (hY : TensorNormalized a Y tY)
    (hlam : PullNormalized a f lam) :
    IsIso (scalarRestrictionPush a f) ∧
    ScalarMatePullEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      (V a Y).map ((rho a f lam).app K) ≫
          (scalarRestrictionPush a f).app ((D a X).obj K) ≫
          (F Λ f).map (tX.derived.hom.app K) =
        tY.derived.hom.app ((F Λ f).obj K) ≫ scalarProjection a f K) ∧
    ScalarMateSectionEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      IsIso ((rho a f lam).app K) ↔ IsIso (scalarProjection a f K)) ∧
    (∀ (K K' : DerivedCategory (Modules Λ X)) (q : K ⟶ K'),
      ((CondensedRing.derivedTensor Λ Y).map ((F Λ f).map q)).app (B a Y) ≫
        scalarProjection a f K' =
        scalarProjection a f K ≫
          (F Λ f).map (((CondensedRing.derivedTensor Λ X).map q).app (B a X))) := by
  have hpull : ScalarMatePullEquation a f tX tY lam := by
    intro M
    simpa only [scalarPullLeft, scalarPullRight, scalarTensorPull,
      scalarCoefficientPull, scalarCoefficientUnit, scalarRestrictionPull, id_eq,
      L, CondensedRing.moduleObjectDerivedPullback, Functor.comp_obj,
      tensorRight, Functor.flip_obj_obj] using
      scalar_tensor_pull_normalization a f tX tY lam hX hY hlam M
  have hmate : scalarRestrictionPush a f = (restrictPush a f lam).hom :=
    scalar_restriction_mate_normalization a f lam hlam
  have hpush : IsIso (scalarRestrictionPush a f) := by
    rw [hmate]
    infer_instance
  have hproj : ∀ K : DerivedCategory (Modules Λ X),
      (V a Y).map ((rho a f lam).app K) ≫
          (scalarRestrictionPush a f).app ((D a X).obj K) ≫
          (F Λ f).map (tX.derived.hom.app K) =
        tY.derived.hom.app ((F Λ f).obj K) ≫ scalarProjection a f K := by
    intro K
    apply ((adj Λ f).homEquiv _ _).symm.injective
    change (L Λ f).map _ ≫ (adj Λ f).counit.app _ =
      (L Λ f).map _ ≫ (adj Λ f).counit.app _
    have ha := restricted_mate_adjunct (adj Λ f) (adj Λ' f)
      (scalarRestrictionPull a f) lam.hom tX.derived.hom K
    dsimp only [tensorRight, Functor.flip_obj_obj] at ha ⊢
    unfold rho scalarRestrictionPush
    rw [ha]
    have hh := hpull ((F Λ f).obj K)
    unfold scalarPullLeft at hh
    rw [← Category.assoc] at hh
    rw [← Category.assoc, ← Category.assoc, hh]
    unfold scalarPullRight scalarProjection
    rw [Functor.map_comp]
    simp only [Category.assoc]
    have hm := modified_projection_adjunct (adj Λ f)
      (CondensedRing.derivedTensor Λ X) (CondensedRing.derivedTensor Λ Y)
      (CondensedRing.leftDerivedUpperStarTensor Λ f) K (B a Y)
      (scalarCoefficientPull a f).hom
    change (L Λ f).map
        (CondensedRing.moduleObjectProjectionMap Λ f K (B a Y) ≫
          (F Λ f).map (((CondensedRing.derivedTensor Λ X).obj K).map
            (scalarCoefficientPull a f).hom)) ≫ (adj Λ f).counit.app _ = _ at hm
    rw [hm]
    simp only [scalarTensorPull]
    congr 1
    congr 1
    exact whisker_exchange ((adj Λ f).counit.app K)
      (scalarCoefficientPull a f).hom
  refine ⟨hpush, hpull, hproj, ?_, ?_, ?_⟩
  · intro K
    unfold scalarSectionLeft scalarSectionRight
    rw [Functor.map_comp, Functor.map_comp]
    rw [← Functor.map_comp, ← Functor.map_comp, hproj K, Functor.map_comp]
    simp only [Category.assoc]
    rw [projection_section_transport]
  · intro K
    let := restriction_reflects a Y
    have h := hproj K
    constructor
    · intro hi
      have := hi
      have : IsIso (tY.derived.hom.app ((F Λ f).obj K) ≫ scalarProjection a f K) := by
        rw [← h]
        infer_instance
      exact IsIso.of_isIso_comp_left (tY.derived.hom.app ((F Λ f).obj K)) _
    · intro hi
      have := hi
      have : IsIso ((V a Y).map ((rho a f lam).app K) ≫
          (scalarRestrictionPush a f).app ((D a X).obj K) ≫
          (F Λ f).map (tX.derived.hom.app K)) := by
        rw [h]
        infer_instance
      have : IsIso ((V a Y).map ((rho a f lam).app K)) :=
        IsIso.of_isIso_comp_right _
          ((scalarRestrictionPush a f).app ((D a X).obj K) ≫
            (F Λ f).map (tX.derived.hom.app K))
      exact isIso_of_reflects_iso _ (V a Y)
  · intro K K' q
    unfold scalarProjection
    have h := NatTrans.congr_app
      (((adj Λ f).rightAdjointProjectionMap
        (T_C := CondensedRing.derivedTensor Λ X)
        (T_D := CondensedRing.derivedTensor Λ Y)
        (CondensedRing.leftDerivedUpperStarTensor Λ f)).naturality q) (B a Y)
    dsimp only [NatTrans.comp_app, Functor.comp_map, Functor.postcompose₂,
      Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
      Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at h
    change (((CondensedRing.derivedTensor Λ Y).map ((F Λ f).map q)).app (B a Y)) ≫
        CondensedRing.moduleObjectProjectionMap Λ f K' (B a Y) =
      CondensedRing.moduleObjectProjectionMap Λ f K (B a Y) ≫
        (F Λ f).map (((CondensedRing.derivedTensor Λ X).map q).app
          ((L Λ f).obj (B a Y))) at h
    rw [← Category.assoc, h]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 2
    exact (((CondensedRing.derivedTensor Λ X).map q).naturality
      (scalarCoefficientPull a f).hom).symm

end AlgebraicGeometry.ProEtale.QuotientChange
