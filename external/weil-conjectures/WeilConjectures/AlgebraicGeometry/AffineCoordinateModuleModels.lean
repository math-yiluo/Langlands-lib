/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonData
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.Algebra.Homology.KFlatPullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Concrete module models for affine coordinates
Source: Stacks Project, Tags 08DW and 06Y1.
(blueprint: lem-pc-affine-coordinate-module-models). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Tilde followed by the supplied coordinate isomorphism's pushforward. 
(blueprint: lem-pc-affine-coordinate-module-models)
-/
noncomputable abbrev affineCoordinateModules (a : AffineComparisonCoordinate.{u, w}) :
    ModuleCat.{u} a.A ⥤ SheafOfModules.{u} (moduleRings a.X.toRingedSpace) :=
  tilde.functor a.A ⋙ SheafOfModules.pushforward a.σ.hom.toRingCatSheafHom

/-- The termwise concrete module model. 
(blueprint: lem-pc-affine-coordinate-module-models)
-/
noncomputable abbrev affineCoordinateComplex (a : AffineComparisonCoordinate.{u, w}) :
    CochainComplex (ModuleCat.{u} a.A) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings a.X.toRingedSpace)) ℤ :=
  (@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} a.A)
    (SheafOfModules.{u} (moduleRings (Spec a.A).toRingedSpace)) _ _ _ _
    (tilde.functor a.A) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
    (@Functor.mapHomologicalComplex ℤ
      (SheafOfModules.{u} (moduleRings (Spec a.A).toRingedSpace))
      (SheafOfModules.{u} (moduleRings a.X.toRingedSpace)) _ _ _ _
      (SheafOfModules.pushforward a.σ.hom.toRingCatSheafHom)
      ⟨fun _ _ ↦ rfl⟩ (.up ℤ))

/-- The concrete module chart preserves zero maps. 
(blueprint: lem-pc-affine-coordinate-module-models)
-/
instance affineCoordinateModules_preservesZero (a : AffineComparisonCoordinate.{u, w}) :
    (affineCoordinateModules a).PreservesZeroMorphisms where
  map_zero := by
    intro M N
    change (SheafOfModules.pushforward a.σ.hom.toRingCatSheafHom).map (tilde.map 0) = 0
    rw [tilde.map_zero]
    rfl

/-- Termwise application of the composite chart agrees with its two explicit factors. 
(blueprint: lem-pc-affine-coordinate-module-models)
-/
noncomputable def affineCoordinateComplexFactorIso (a : AffineComparisonCoordinate.{u, w}) :
    (affineCoordinateModules a).mapHomologicalComplex (.up ℤ) ≅
      affineCoordinateComplex a :=
  NatIso.ofComponents (fun M ↦ HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ Iso.refl _) (by intros; simp)) (by intros; ext i; rfl)

/-- The supplied localized model is naturally its concrete module model's localization.
Source: Stacks Project, Tag 08DW; the supplied hd and hH.
(blueprint: lem-pc-affine-coordinate-module-models). -/
noncomputable def affineCoordinateModelIso (a : AffineComparisonCoordinate.{u, w}) :
    a.H ≅ affineCoordinateComplex a ⋙ DerivedCategory.Q :=
  a.hH ≪≫ Functor.isoWhiskerLeft _ a.hd

/-- Pushforward along an isomorphism, with inverse pushforward. 
(blueprint: lem-pc-affine-coordinate-module-models)
-/
noncomputable def affineCoordinateModuleEquivalence {X Y : Scheme.{u}} (s : X ≅ Y) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Scheme.Modules.pushforwardComp s.hom s.inv ≪≫
      Scheme.Modules.pushforwardCongr s.hom_inv_id ≪≫ Scheme.Modules.pushforwardId X).symm)
    (Scheme.Modules.pushforwardComp s.inv s.hom ≪≫
      Scheme.Modules.pushforwardCongr s.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Y)

/-- Concrete coordinate models preserve K-flatness.
Source: Stacks Project, Tags 06Y1 and 08DW.
(blueprint: lem-pc-affine-coordinate-module-models).
Proof: tilde of M is K-flat. Pushforward along a scheme isomorphism is the inverse
of the opposite pushforward equivalence, hence is isomorphic, by uniqueness of
left adjoints, to tensor pullback along the inverse isomorphism. Pullback preserves
K-flatness. The termwise comparison and invariance under isomorphism give the result. -/
theorem affineCoordinateComplex_isKFlat (a : AffineComparisonCoordinate.{u, w})
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) (hM : AffineComparisonKFlat a.A M) :
    CochainComplex.IsKFlatTensor (R := a.X.sheaf) ((affineCoordinateComplex a).obj M) := by
  let T := @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} a.A)
    (SheafOfModules.{u} (moduleRings (Spec a.A).toRingedSpace)) _ _ _ _
    (tilde.functor a.A) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have hT : CochainComplex.IsKFlatTensor (R := (Spec a.A).sheaf) (T.obj M) :=
    isKFlat_tilde a.A M hM
  let e := affineCoordinateModuleEquivalence a.σ
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a.σ.inv
  let θ : e.functor ≅ Scheme.Modules.tensorPullback a.σ.inv :=
    e.toAdjunction.leftAdjointUniq adj
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : (Scheme.Modules.tensorPullback a.σ.inv).Additive := Functor.additive_of_iso θ
  let q := (NatIso.mapHomologicalComplex θ (.up ℤ)).app (T.obj M)
  have hP : CochainComplex.IsKFlatTensor (R := a.X.sheaf)
      (((Scheme.Modules.tensorPullback a.σ.inv).mapHomologicalComplex (.up ℤ)).obj
        (T.obj M)) := by
    have h := CochainComplex.isKFlat_pullback a.σ.inv.base a.X.sheaf
      (Spec a.A).sheaf ⟨a.σ.inv.c⟩ (T.obj M) hT
    convert h using 1
    rfl
  let := SheafOfModules.monoidalCategory a.X.sheaf
  intro F hF i
  exact (hP F hF i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso q.symm)

end AlgebraicGeometry
