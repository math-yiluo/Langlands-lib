/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Counit-normalized affine derived tensor source -/
@[expose] public section
set_option autoImplicit false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

local instance (priority := 2000) sourceCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance (priority := 2000) sourceCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance (priority := 2000) sourceCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))


local instance sourceComparisonTildeAdditive (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).Additive := by
  constructor
  intro M N f g
  exact tilde.map_add (R := .of C) f g
local instance sourceComparisonTildeHomology (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).PreservesHomology := tilde_preservesHomology C
local instance sourceComparisonTildeLimits (C : Type u) [CommRing C] :
    PreservesFiniteLimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteLimits_of_preservesHomology
local instance sourceComparisonTildeColimits (C : Type u) [CommRing C] :
    PreservesFiniteColimits (affinePushforwardTilde C) :=
  (affinePushforwardTilde C).preservesFiniteColimits_of_preservesHomology

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

local instance sourceComparisonHasDerivedCategory (Y : Scheme.{u}) :
    HasDerivedCategory.{w} Y.Modules :=
  (‹∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))›) Y

local instance sourceComparisonPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
set_option linter.unusedSectionVars false in
set_option linter.overlappingInstances false in
/-- (blueprint: lem-pc-affine-tilde-tensor-source-comparison) -/
theorem exists_affineTildeTensorSourceComparison
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
  have h := exists_affineTildeTensorSourceComparisonCore R A B D M m F₀ hF₀
  let χ := Classical.choose h
  refine ⟨χ, ?_⟩
  intro φ ψ hw
  exact Classical.choose_spec h φ ψ hw

end AlgebraicGeometry

