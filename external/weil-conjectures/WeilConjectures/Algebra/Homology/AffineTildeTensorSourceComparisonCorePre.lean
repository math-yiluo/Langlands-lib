/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization


public import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

local instance preSourceCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance preSourceCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance preSourceCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))
local instance preTildeAdditive (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).Additive := by
  constructor
  intro M N f g
  exact tilde.map_add (R := .of C) f g
local instance preTildeHomology (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).PreservesHomology := tilde_preservesHomology C
local instance preTildeLimits (C : Type u) [CommRing C] :
    PreservesFiniteLimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteLimits_of_preservesHomology
local instance preTildeColimits (C : Type u) [CommRing C] :
    PreservesFiniteColimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteColimits_of_preservesHomology
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
local instance prePullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f


attribute [local irreducible] tilde tilde.functor Functor.mapDerivedCategory
  affineTildePushforwardComparison Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Scheme.Modules.tensorPullback schemeDerivedBaseChangeMap moduleHomotopyBaseChange
  affineTildeTensorOrdinarySourceIso affineTildeTensorDerivedCounit

-- Comparing affine tensor units and counits requires substantial reduction.
/-- The source counit comparison before the affine pushforward unit and square transport.
Source: Stacks Project, Tags 06Y6, 08DW and 0AVW.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison).
This is the strict precomparison used to construct the target source isomorphism. -/
theorem affineTildeTensorSourcePrecomparison
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let _H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)
    let qs := HomotopyCategory.quotient (Spec (.of R)).Modules (.up ℤ)
    ∃ χpre : (affinePushforwardTilde B).mapDerivedCategory.obj
        (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
            (.up ℤ)).obj M)))) ≅
      (derivedPullback g).obj (DerivedCategory.Q.obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M))),
      χpre.hom ≫ cast (by rfl) ((SingleComplexBaseChange.counit g).app
          (qs.obj (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
              (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)))) =
        affineTildeTensorDerivedCounit R A B D M m
          (affinePushforwardTilde B).mapDerivedCategory rfl ≫
          DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom := by
  classical
  let d := (‹∀ Y : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))›)
  let : HasDerivedCategory.{w} (Spec (.of R)).Modules := d _
  let : HasDerivedCategory.{w} (Spec (.of A)).Modules := d _
  let : HasDerivedCategory.{w} (Spec (.of B)).Modules := d _
  let : HasDerivedCategory.{w} (Spec (.of D)).Modules := d _
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let C := ((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M
  let H := (HomotopyCategory.quotient _ (.up ℤ)).obj C
  let N := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj M
  let E := ModuleCat.extendScalars (algebraMap R B)
  let T := affinePushforwardTilde B
  let TR := affinePushforwardTilde R
  let P := Scheme.Modules.pushforward f
  let PB := Scheme.Modules.tensorPullback g
  let RC := TR.mapHomologicalComplex (.up ℤ)
  let EC := E.mapHomologicalComplex (.up ℤ)
  let TC := T.mapHomologicalComplex (.up ℤ)
  let PC := P.mapHomologicalComplex (.up ℤ)
  let PBC := PB.mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let qs := HomotopyCategory.quotient (Spec (.of R)).Modules (.up ℤ)
  let : PB.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} g
  let : (E ⋙ T).Additive := inferInstance
  let : P.Additive := inferInstance
  let : (affinePushforwardTilde A ⋙ P).Additive := inferInstance
  let : (affinePushforwardTilde A ⋙ P).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by
      rw [Functor.comp_map, (affinePushforwardTilde A).map_zero]
      exact P.map_zero _ _⟩
  let θ : TR ⋙ PB ≅ E ⋙ T :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
      (CommRingCat.ofHom (algebraMap R B)))
  let δ := (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app N
  let σ : RC.obj N ≅ PC.obj C :=
    (Functor.mapHomologicalComplexCompIso
      (affineTildePushforwardComparison A R (algebraMap R A)) (.up ℤ)).app M
  let c := T.mapDerivedCategory.{wM, w}.map (m.counit.app (q.obj N)) ≫
    (T.mapDerivedCategoryFactors.{wM, w}.app (EC.obj N)).hom
  obtain ⟨e, he⟩ := affineTilde_scalarExtension_comparison R B
    m.derived m.counit m.universal N
  change e.hom ≫ (SingleComplexBaseChange.counit g).app (qs.obj (RC.obj N)) ≫
    DerivedCategory.Q.map δ.hom = c at he
  have he' : e.hom ≫ (SingleComplexBaseChange.counit g).app (qs.obj (RC.obj N)) =
      c ≫ DerivedCategory.Q.map δ.inv := by
    exact (Iso.eq_comp_inv (DerivedCategory.Q.mapIso δ)).2
      ((Category.assoc _ _ _).trans he)
  let χpre := e ≪≫ (derivedPullback g).mapIso (DerivedCategory.Q.mapIso σ)
  have hn := leftCounit_naturality PB (derivedPullback g)
    (SingleComplexBaseChange.counit g) σ.hom
  have ho : δ.inv ≫ PBC.map σ.hom =
      (affineTildeTensorOrdinarySourceIso R A B M).hom := by
    unfold affineTildeTensorOrdinarySourceIso
    rfl
  have hc : χpre.hom ≫ (SingleComplexBaseChange.counit g).app (qs.obj (PC.obj C)) =
      c ≫ DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom := by
    dsimp only [χpre, Iso.trans_hom, Functor.mapIso_hom]
    erw [Category.assoc, hn, ← Category.assoc, he']
    rw [Category.assoc, ← DerivedCategory.Q.map_comp, ho]
  have hdc : affineTildeTensorDerivedCounit R A B D M m
      T.mapDerivedCategory.{wM, w} rfl = c := by
    unfold affineTildeTensorDerivedCounit
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  refine ⟨χpre, ?_⟩
  with_unfolding_all simpa only [cast_eq, f, g, C, H, N, E, T, TR, P, PB, RC, EC, TC,
    PC, PBC, q, qs, Category.assoc] using hc.trans (congrArg (fun z ↦ z ≫
      DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom) hdc.symm)


end AlgebraicGeometry
