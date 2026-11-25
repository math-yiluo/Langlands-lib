/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore

/-! # K-flat module models on affine schemes

Source: Stacks Project, perfect.tex, Tags 06Z0 and 08DV.
(blueprint: lem-pc-affine-qcoh-complex-model).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- Every quasi-coherent affine derived object has a K-flat module-complex model.
Source: Stacks, perfect.tex, Tag 06Z0.
(blueprint: lem-pc-affine-qcoh-complex-model).
Proof: Apply the inverse of the affine quasi-coherent derived equivalence to Q.
The localization functor from module complexes to their derived category is
essentially surjective, so represent that inverse by a complex M. Apply the
functor comparison with termwise tilde to this representative and then the
counit of the equivalence. Resolve M by a K-flat module complex P. The
localization and the equivalence invert its augmentation, and naturality of
the tilde comparison identifies its image with Q of tilde of that augmentation.
Compose with the inverse of this image to obtain the asserted isomorphism.
This includes the zero complex and uses no boundedness condition. -/
theorem exists_affineQCohComplexModel
    {R : CommRingCat.{u}} (Q : schemeDerivedCategory (Spec R))
    (hQ : schemeDerivedQCohProperty (Spec R) Q) :
    ∃ M : CochainComplex (ModuleCat.{u} R) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat M ∧
      Nonempty (Q ≅ DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} R ⥤
              SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
              (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)) := by
  classical
  obtain ⟨a, ⟨α⟩, _, _⟩ := exists_affineQCohDerivedEquivalence_core R
  let K : schemeDerivedQCohCategory (Spec R) := ⟨Q, hQ⟩
  let D := a.inverse.obj K
  let M := DerivedCategory.Q.objPreimage D
  let β := a.functor.mapIso (DerivedCategory.Q.objObjPreimageIso D) ≪≫ a.counitIso.app K
  let γ := (schemeDerivedQCohProperty (Spec R)).ι.mapIso β.symm ≪≫ α.app M
  obtain ⟨P, π, hπ, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat M
  have : QuasiIso π := hπ
  have hleft : IsIso ((DerivedCategory.Q ⋙ a.functor ⋙
      (schemeDerivedQCohProperty (Spec R)).ι).map π) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have hright := (NatIso.isIso_map_iff α π).mp hleft
  exact ⟨P, hP, ⟨γ ≪≫ (asIso ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} R ⥤
      SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
      (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ) ⋙
        DerivedCategory.Q).map π)).symm⟩⟩

end AlgebraicGeometry
