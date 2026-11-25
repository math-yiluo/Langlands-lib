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
import WeilConjectures.Algebra.Homology.AffineTildePushforwardHomologyFactorization

/-! # Homology coordinates of the raw affine tensor comparison

Source: Stacks Project, Tags 0DJ8, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-coefficient-pushforward-homology-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

local instance (priority := 2000) coefficientCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance (priority := 2000) coefficientCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance (priority := 2000) coefficientCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  affineTildePushforwardComparison
  affinePushforwardCohomologyMapOfComparison

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Ordinary coefficient maps followed by the pushforward homology comparison.
Source: Stacks Project, Tags 06Z0 and 0AVW; parent proof step 2.
(blueprint: lem-pc-affine-tilde-coefficient-pushforward-homology-coordinates).

Proof: Put v = s followed by restriction of z₀. Apply the factorization of the
pushforward homology map into the inverse restriction homology comparison,
inverse exact tilde comparison, inverse quotient comparison, termwise ordinary
comparison and derived unit. Expand cE and s, use functoriality of restriction
and tilde, and reassociate. The result uses only ordinary module comparison
maps: neither the derived tensor counit nor its cohomology identification occurs.
No invertibility of the module comparison is needed. Zero complexes and zero
rings satisfy the same functoriality and exactness identities. -/
theorem affineTildeCoefficientPushforwardHomologyCoordinates
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ) (i : ℤ) :
    let α := algebraMap (A ⊗[R] B) D
    let j : B →+* A ⊗[R] B := Algebra.TensorProduct.includeRight.toRingHom
    let T := affinePushforwardTilde B
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
    let C := (((ModuleCat.extendScalars (α.comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj M)
    let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    let ρ := ModuleCat.restrictScalarsComp' j α ψ hψ.symm
    let z₀ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i).map
      (eqToHom (by dsimp only [C, α]; rw [hφ] : C = Cg))
    let V := ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj Cg
    let _ : (affinePushforwardTilde B).Additive := by
      constructor
      intro M N f g
      exact tilde.map_add (R := .of B) f g
    let _ : (affinePushforwardTilde B).PreservesHomology := tilde_preservesHomology B
    let _ : (affinePushforwardTilde D).Additive := by
      constructor
      intro M N f g
      exact tilde.map_add (R := .of D) f g
    let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))
    let _ : P.Additive := inferInstance
    let _ : (affinePushforwardTilde D ⋙ P).PreservesZeroMorphisms :=
      ⟨fun _ _ ↦ by
        rw [Functor.comp_map, (affinePushforwardTilde D).map_zero]
        exact P.map_zero _ _⟩
    let a := ((affineTildePushforwardComparison D B ψ).hom.mapHomologicalComplex
      (.up ℤ)).app Cg
    let β := (RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affinePushforwardTilde D).mapHomologicalComplex (.up ℤ)).obj Cg))
    T.map ((ModuleCat.restrictScalars j).map (m.comparison i) ≫
        (ModuleCat.restrictScalars j).map
          (HomologicalComplex.homologyMap m.ordinaryToLocalized i ≫
            ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom) ≫
        ρ.inv.app (C.homology i) ≫ (ModuleCat.restrictScalars ψ).map z₀ ≫
        ((Cg.sc i).mapHomologyIso (ModuleCat.restrictScalars ψ)).inv) ≫
      ((V.sc i).mapHomologyIso (affinePushforwardTilde B)).inv ≫
      (DerivedCategory.homologyFunctorFactors _ i).inv.app
        (((affinePushforwardTilde B).mapHomologicalComplex (.up ℤ)).obj V) ≫
      H.map (DerivedCategory.Q.map a) ≫ cast (by rfl) (H.map β) =
      T.map ((ModuleCat.restrictScalars j).map (m.comparison i)) ≫
      T.map ((ModuleCat.restrictScalars j).map
        (HomologicalComplex.homologyMap m.ordinaryToLocalized i)) ≫
      T.map ((ModuleCat.restrictScalars j).map
        ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom) ≫
      T.map (ρ.inv.app (C.homology i)) ≫
      T.map ((ModuleCat.restrictScalars ψ).map z₀) ≫
        affineTildePushforwardCohomologyMap D B ψ Cg i := by
  let T := affinePushforwardTilde B
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : T.PreservesHomology := tilde_preservesHomology B
  let : (affinePushforwardTilde D).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of D) f g
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))
  let : P.Additive := inferInstance
  let : (affinePushforwardTilde D ⋙ P).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by
      rw [Functor.comp_map, (affinePushforwardTilde D).map_zero]
      exact P.map_zero _ _⟩
  let α := algebraMap (A ⊗[R] B) D
  let j : B →+* A ⊗[R] B := Algebra.TensorProduct.includeRight.toRingHom
  let C := ((ModuleCat.extendScalars (α.comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
    (.up ℤ)).obj M
  let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let ρ := ModuleCat.restrictScalarsComp' j α ψ hψ.symm
  let z₀ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i).map
    (eqToHom (by dsimp only [C, α]; rw [hφ] : C = Cg))
  let v := (ModuleCat.restrictScalars j).map (m.comparison i) ≫
    (ModuleCat.restrictScalars j).map
      (HomologicalComplex.homologyMap m.ordinaryToLocalized i ≫
        ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom) ≫
    ρ.inv.app (C.homology i) ≫ (ModuleCat.restrictScalars ψ).map z₀
  have h := affineTildePushforwardHomologyFactorization D B ψ Cg i _ v
  simpa only [v, Functor.map_comp, Category.assoc] using h

end AlgebraicGeometry
