/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility

/-! # Core affine derived tensor source comparison -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

local instance coreSourceCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance coreSourceCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance coreSourceCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))
local instance coreTildeAdditive (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).Additive := by
  constructor
  intro M N f g
  exact tilde.map_add (R := .of C) f g
local instance coreTildeHomology (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).PreservesHomology := tilde_preservesHomology C
local instance coreTildeLimits (C : Type u) [CommRing C] :
    PreservesFiniteLimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteLimits_of_preservesHomology
local instance coreTildeColimits (C : Type u) [CommRing C] :
    PreservesFiniteColimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteColimits_of_preservesHomology
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
local instance coreSourceComparisonHasDerivedCategory (Y : Scheme.{u}) :
    HasDerivedCategory.{w} Y.Modules :=
  (‹∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))›) Y

local instance corePullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem normalized_unit_exchange
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {N N' : C} {X Y Z T V : D} (e : X ≅ L.obj N) (u : N ⟶ N') [IsIso u]
    (b : L.obj N' ⟶ Y) (a : Y ⟶ Z) (ε : L.obj N ⟶ T)
    (c : X ⟶ V) (o : V ⟶ T) (d : T ⟶ Z)
    (hc : e.hom ≫ ε = c ≫ o) (hb : L.map u ≫ b ≫ a = ε ≫ d) :
    (e ≪≫ L.mapIso (asIso u)).hom ≫ b ≫ a = c ≫ o ≫ d := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
  rw [hb, ← Category.assoc, hc, Category.assoc]
attribute [local irreducible] tilde tilde.functor Functor.mapDerivedCategory
  affineTildePushforwardComparison Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Scheme.Modules.tensorPullback schemeDerivedBaseChangeMap moduleHomotopyBaseChange
  affineTildeTensorOrdinarySourceIso affineTildeTensorDerivedCounit

-- Comparing affine tensor units and counits requires substantial reduction.
/-- The affine source comparison is normalized by its derived counit.
Source: Stacks Project, Tags 06Y6, 08DW, 06Z0, 08D4, 08HY and 0AVW.
(blueprint: lem-pc-affine-tilde-tensor-source-comparison).

Proof: first transport along the supplied defining equality of F0.
Resolve the R-restriction of M by a termwise flat K-flat complex P.
The universal counit of m identifies its value on this restriction with the
B-extension of P. Exact tilde sends the augmentation to a quasi-isomorphism.
Its K-flat image computes g-pullback, with the unit-normalized tensor/tilde
identification. Naturality of the two universal counits gives the displayed
normalization equation; comparison on P determines it after localization.
Compose the tensor comparison with pullback of the concrete ordinary affine
pushforward iso. The actual affine pushforward right-derived unit is invertible:
choose a K-injective resolution, apply affinePushforward_resolution_quasiIso,
and use naturality of the unit. Pullback of this unit gives chi with the stated
source. For every commutative affine square, apply the pinned derived-unit
compatibility theorem. Precompose its equality with the source comparison;
the counit normalization proved above gives the displayed universal equation.
This equation involves ordinary exchange, and does not identify the coefficient
map or assert the final mate equality. No boundedness is imposed. For the zero complex and zero
rings the same counit equations hold on the unique zero objects. -/
theorem exists_affineTildeTensorSourceComparisonCore
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (F₀ : DerivedCategory.{wM} (ModuleCat.{u} B) ⥤
      schemeDerivedCategory.{u, w} (Spec (.of B)))
    (hF₀ : F₀ = Functor.mapDerivedCategory.{wM, w} (affinePushforwardTilde B)) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)
    ∃ χ : F₀.obj
          (m.derived.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
            (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
              (.up ℤ)).obj M)))) ≅
        (derivedPullback g).obj ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj H)),
      ∀ (φ : A →+* D) (ψ : B →+* D)
        (hw : Spec.map (CommRingCat.ofHom φ) ≫ f =
          Spec.map (CommRingCat.ofHom ψ) ≫ g),
        let p := Spec.map (CommRingCat.ofHom φ)
        let f' := Spec.map (CommRingCat.ofHom ψ)
        χ.hom ≫ schemeDerivedBaseChangeMap f f' g p hw (DerivedCategory.Qh.obj H) ≫
          (schemeDerivedDirectImage f').map ((SingleComplexBaseChange.counit p).app H) =
        affineTildeTensorDerivedCounit R A B D M m F₀ hF₀ ≫
          DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom ≫
          cast (by rfl) (DerivedCategory.Qh.{w}.map
            ((moduleHomotopyBaseChange f f' g p hw).app H)) ≫
          (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
            (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H) := by
  classical
  subst F₀
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
  let P := Scheme.Modules.pushforward f
  let PB := Scheme.Modules.tensorPullback g
  let PC := P.mapHomologicalComplex (.up ℤ)
  let qs := HomotopyCategory.quotient (Spec (.of R)).Modules (.up ℤ)
  let : PB.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} g
  let : (E ⋙ T).Additive := inferInstance
  let : P.Additive := inferInstance
  let : (affinePushforwardTilde A ⋙ P).Additive := inferInstance
  let : (affinePushforwardTilde A ⋙ P).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by
      rw [Functor.comp_map, (affinePushforwardTilde A).map_zero]
      exact P.map_zero _ _⟩
  let U := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let unit := U.rightDerivedFunctorUnit.{_, _, _, _, w, w}.app H
  have hu : IsIso unit := by
    exact affineTilde_pushforward_unit_isIso R A M
  let χpre := Classical.choose (affineTildeTensorSourcePrecomparison R A B D M m)
  have hχpre := Classical.choose_spec (affineTildeTensorSourcePrecomparison R A B D M m)
  have hc : χpre.hom ≫ (SingleComplexBaseChange.counit g).app (qs.obj (PC.obj C)) =
      affineTildeTensorDerivedCounit R A B D M m (affinePushforwardTilde B).mapDerivedCategory rfl ≫
        DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom := by
    exact hχpre
  let χ := χpre ≪≫ (derivedPullback g).mapIso (asIso unit)
  refine ⟨χ, ?_⟩
  intro φ ψ hw
  let p := Spec.map (CommRingCat.ofHom φ)
  let f' := Spec.map (CommRingCat.ofHom ψ)
  have hb : (derivedPullback g).map unit ≫
      schemeDerivedBaseChangeMap f f' g p hw (DerivedCategory.Qh.obj H) ≫
      (schemeDerivedDirectImage f').map ((SingleComplexBaseChange.counit p).app H) =
    (SingleComplexBaseChange.counit g).app (qs.obj (PC.obj C)) ≫
      DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p hw).app H) ≫
      (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H) := by
    exact @derivedBaseChange_unit_compatibility.{u, w} d _ _ _ _ f f' g p hw _ _ H
  exact normalized_unit_exchange (derivedPullback g) χpre unit
    (schemeDerivedBaseChangeMap f f' g p hw (DerivedCategory.Qh.obj H))
    ((schemeDerivedDirectImage f').map ((SingleComplexBaseChange.counit p).app H))
    ((SingleComplexBaseChange.counit g).app (qs.obj (PC.obj C)))
    (affineTildeTensorDerivedCounit R A B D M m
      (affinePushforwardTilde B).mapDerivedCategory rfl)
    (DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom)
    (DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p hw).app H) ≫
      (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H)) hc hb


end AlgebraicGeometry
