/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-! # Counit-normalized affine derived tensor source

Source: Stacks Project, Tags 06Y6, 08DW and 06Z0.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

@[reducible]
local instance (priority := 2000) prebaseSourceCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
@[reducible]
local instance (priority := 2000) prebaseSourceCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
@[reducible]
local instance (priority := 2000) prebaseSourceCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))


local instance prebaseSourceComparisonTildeAdditive (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).Additive := by
  constructor
  intro M N f g
  exact tilde.map_add (R := .of C) f g
local instance prebaseSourceComparisonTildeHomology (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).PreservesHomology := tilde_preservesHomology C
local instance prebaseSourceComparisonTildeLimits (C : Type u) [CommRing C] :
    PreservesFiniteLimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteLimits_of_preservesHomology
local instance prebaseSourceComparisonTildeColimits (C : Type u) [CommRing C] :
    PreservesFiniteColimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteColimits_of_preservesHomology

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

local instance prebaseSourceComparisonPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f

attribute [local irreducible] tilde tilde.functor Functor.mapDerivedCategory
  affineTildePushforwardComparison Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Scheme.Modules.tensorPullback schemeDerivedBaseChangeMap moduleHomotopyBaseChange

/-- Ordinary source identification: inverse tensor/tilde comparison followed by
pullback of the affine pushforward comparison. This is a concrete construction.
Source: Stacks Project, Tags 01I9 and 08DW.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison). -/
def affineTildeTensorOrdinarySourceIso
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((affinePushforwardTilde B).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ≅
    ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).mapHomologicalComplex (.up ℤ)).obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let : (Scheme.Modules.tensorPullback g).Additive :=
    SingleComplexBaseChange.tensorPullbackAdditive.{u, w} g
  let N := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
    (.up ℤ)).obj M
  let : (affinePushforwardTilde R).Additive := prebaseSourceComparisonTildeAdditive R
  let : (affinePushforwardTilde B).Additive := prebaseSourceComparisonTildeAdditive B
  let : (ModuleCat.extendScalars.{u, u, u} (algebraMap R B)).Additive :=
    ModuleCat.baseDerivedTensor_extendScalars_additive _
  let θ : affinePushforwardTilde R ⋙ Scheme.Modules.tensorPullback g ≅
      ModuleCat.extendScalars (algebraMap R B) ⋙ affinePushforwardTilde B :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom (algebraMap R B)))
  let δ := (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app N
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  let : (affinePushforwardTilde A).Additive := prebaseSourceComparisonTildeAdditive A
  let : P.Additive := inferInstance
  let : (affinePushforwardTilde A ⋙ P).Additive := inferInstance
  let : (affinePushforwardTilde A ⋙ P).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by
      rw [Functor.comp_map, (affinePushforwardTilde A).map_zero]
      exact P.map_zero _ _⟩
  let s : ((affinePushforwardTilde R).mapHomologicalComplex (.up ℤ)).obj N ≅
      (P.mapHomologicalComplex (.up ℤ)).obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M) :=
    (Functor.mapHomologicalComplexCompIso
      (affineTildePushforwardComparison A R (algebraMap R A)) (.up ℤ)).app M
  exact δ.symm ≪≫
    ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).mapIso s

/-- The first two factors of the raw tensor map, before any coefficient map.
Source: Stacks Project, Tags 06Y6 and 06Z0.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison). -/
def affineTildeTensorDerivedCounit
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (F₀ : DerivedCategory.{wM} (ModuleCat.{u} B) ⥤
      schemeDerivedCategory.{u, w} (Spec (.of B)))
    (hF₀ : F₀ = Functor.mapDerivedCategory.{wM, w} (affinePushforwardTilde B)) :
    F₀.obj
      (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)))) ⟶
    DerivedCategory.Q.obj
      (((affinePushforwardTilde B).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).obj M))) := by
  let N := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj M
  let N' := ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj N
  exact eqToHom (congrArg (fun G ↦ G.obj
      (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj N)))) hF₀) ≫
    (affinePushforwardTilde B).mapDerivedCategory.map
      (cast (by rfl) (m.counit.app ((HomotopyCategory.quotient _ _).obj N))) ≫
    ((affinePushforwardTilde B).mapDerivedCategoryFactors.app N').hom

attribute [local irreducible] affineTildeTensorOrdinarySourceIso
  affineTildeTensorDerivedCounit

theorem affineTilde_scalarExtension_comparison
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (L : DerivedCategory.{wM} (ModuleCat.{u} R) ⥤
      DerivedCategory.{wM} (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)))
    (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    let T := affinePushforwardTilde B
    let TR := affinePushforwardTilde R
    let E := ModuleCat.extendScalars (algebraMap R B)
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let : (Scheme.Modules.tensorPullback g).Additive :=
      SingleComplexBaseChange.tensorPullbackAdditive.{u, w} g
    let : TR.Additive := prebaseSourceComparisonTildeAdditive R
    let : T.Additive := prebaseSourceComparisonTildeAdditive B
    let : E.Additive := ModuleCat.baseDerivedTensor_extendScalars_additive _
    let : (E ⋙ T).Additive := inferInstance
    let θ : TR ⋙ Scheme.Modules.tensorPullback g ≅ E ⋙ T :=
      Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
        (CommRingCat.ofHom (algebraMap R B)))
    let δ := (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app N
    ∃ e : T.mapDerivedCategory.{wM, w}.obj
        (L.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj N))) ≅
      (derivedPullback g).obj (DerivedCategory.Q.obj
        ((TR.mapHomologicalComplex (.up ℤ)).obj N)),
      e.hom ≫ cast (by rfl) ((SingleComplexBaseChange.counit g).app
          ((HomotopyCategory.quotient _ _).obj ((TR.mapHomologicalComplex (.up ℤ)).obj N))) ≫
        DerivedCategory.Q.map δ.hom =
      T.mapDerivedCategory.{wM, w}.map
        (cast (by rfl) (ε.app ((HomotopyCategory.quotient _ _).obj N))) ≫
        (T.mapDerivedCategoryFactors.{wM, w}.app
          ((E.mapHomologicalComplex (.up ℤ)).obj N)).hom := by
  classical
  dsimp only
  let T := affinePushforwardTilde B
  let TR := affinePushforwardTilde R
  let E := ModuleCat.extendScalars (algebraMap R B)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let RC := TR.mapHomologicalComplex (.up ℤ)
  let qs := HomotopyCategory.quotient (Spec (.of R)).Modules (.up ℤ)
  let : (Scheme.Modules.tensorPullback g).Additive :=
    SingleComplexBaseChange.tensorPullbackAdditive.{u, w} g
  let : (E ⋙ T).Additive := inferInstance
  let θ : TR ⋙ Scheme.Modules.tensorPullback g ≅ E ⋙ T :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom (algebraMap R B)))
  obtain ⟨P, s, hs, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat N
  have : QuasiIso s := hs
  have : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) := hL
  have : E.PreservesKFlatQuasiIso := ModuleCat.extendScalars_preservesKFlatQuasiIso _
  have : IsIso (ε.app (q.obj P)) :=
    E.derives_kFlat.isIso_of_isLeftDerivedFunctor ε
      ⟨_, (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP⟩
  have hPa : ∀ Z : CochainComplex (ModuleCat.{u} R) ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z P (MonoidalCategory.curriedTensor _)).Acyclic := by
    intro Z hZ
    have hk := (HomotopyCategory.kFlat_iff_preserves_acyclic (q.obj P)).mp
      ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
      (hk _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mpr hZ)).2
  have hIso : IsIso ((SingleComplexBaseChange.counit g).app (qs.obj (RC.obj P))) :=
    SingleComplexBaseChange.counit_isIso_kFlat g _ (isKFlat_tilde R P hPa)
  exact leftDerived_comparison_on_resolution TR T E (Scheme.Modules.tensorPullback g)
    L (derivedPullback g) ε (SingleComplexBaseChange.counit g) θ s
      (hεgP := hIso)

theorem affineTilde_pushforward_unit_isIso
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    let P := RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).toLRSHom.toShHom
    IsIso (P.rightDerivedFunctorUnit.{_, _, _, _, w, w}.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M))) := by
  let C := ((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M
  let P := RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom (algebraMap R A))).toLRSHom.toShHom
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) (.up ℤ)
  obtain ⟨J, hJ, s, _, hsi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : J.IsKInjective := hJ
  have : QuasiIso s := hsi
  have hC (n : ℤ) : (C.X n).IsQuasicoherent := by
    change ((tilde.functor (.of A)).obj (M.X n)).IsQuasicoherent
    infer_instance
  have hPs : QuasiIso ((P.mapHomologicalComplex (.up ℤ)).map s) :=
    affinePushforward_resolution_quasiIso _ C J hC s
  have hs : IsIso (DerivedCategory.Qh.{w}.map (q.map s)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hsi
  have hPs' : IsIso (DerivedCategory.Qh.{w}.map
      ((P.mapHomotopyCategory (.up ℤ)).map (q.map s))) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hPs
  have : IsIso ((DerivedCategory.Qh.{w} ⋙ P.rightDerivedFunctor.{_, _, _, _, w, w}).map
      (q.map s)) := by
    change IsIso (P.rightDerivedFunctor.map (DerivedCategory.Qh.map (q.map s)))
    infer_instance
  have hn := P.rightDerivedFunctorUnit.{_, _, _, _, w, w}.naturality (q.map s)
  have : IsIso (P.rightDerivedFunctorUnit.{_, _, _, _, w, w}.app (q.obj C) ≫
      (DerivedCategory.Qh.{w} ⋙ P.rightDerivedFunctor.{_, _, _, _, w, w}).map (q.map s)) := by
    rw [← hn]
    dsimp only [Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.Qh.{w} ⋙ P.rightDerivedFunctor.{_, _, _, _, w, w}).map (q.map s))





end AlgebraicGeometry
