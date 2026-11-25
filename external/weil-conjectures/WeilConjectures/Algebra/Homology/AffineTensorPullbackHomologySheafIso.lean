/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates

/-! # Sheaf-level affine ordinary tensor homology coordinates

Source: Stacks Project, Tag 01I9.
(blueprint: new-def-pc-affine-tensor-pullback-homology-sheaf-iso). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Exact tilde homology followed by homology factorization and the inverse
termwise tensor-pullback comparison. Source: Stacks Project, Tag 01I9.
(blueprint: new-def-pc-affine-tensor-pullback-homology-sheaf-iso). -/
def affineTensorPullbackHomologySheafIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let T := ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom φ))).mapHomologicalComplex (.up ℤ)).obj P
    let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    (tilde.functor (.of A')).obj (C.homology i) ≅
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i).obj
          (DerivedCategory.Q.obj T) := by
  let TA : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let TB : ModuleCat.{u} A' ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) := tilde.functor (.of A')
  let : TA.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A) f g
  let : TB.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of A') f g
  let : TA.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesHomology := tilde_preservesHomology A'
  let f := Spec.map (CommRingCat.ofHom φ)
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f
  let θ : TA ⋙ E ≅ ModuleCat.extendScalars φ ⋙ TB :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ))
  let P := (TA.mapHomologicalComplex (.up ℤ)).obj M
  let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let T := (E.mapHomologicalComplex (.up ℤ)).obj P
  let δ : T ≅ (TB.mapHomologicalComplex (.up ℤ)).obj C :=
    (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app M
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
  let d : TB.obj (C.homology i) ≅ H.obj (DerivedCategory.Q.obj T) :=
    ((C.sc i).mapHomologyIso TB).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors _ i).app
        ((TB.mapHomologicalComplex (.up ℤ)).obj C)).symm ≪≫
      H.mapIso (DerivedCategory.Q.mapIso δ).symm
  exact d

end AlgebraicGeometry
