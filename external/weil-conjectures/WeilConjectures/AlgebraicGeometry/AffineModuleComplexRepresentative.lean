/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Module-complex representatives on affine schemes

Source: Stacks Project, Tags 06Z0 and 08DW.
(blueprint: lem-pc-affine-module-complex-representative).
-/

@[expose] public section

universe u w wS

open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- A quasi-coherent derived object on an affine scheme has a module-complex representative.
Source: Stacks Project, Tag 06Z0.
Proof: restriction along the inverse of Y.toSpecΓ is an exact equivalence, preserving
quasi-coherent cohomology. Apply the core affine derived equivalence to this transported
object and essential surjectivity of Q to its inverse image. The equivalence comparison
identifies its image with termwise tilde of a module complex M. Apply exact restriction
back along Y.toSpecΓ and its localization comparison to obtain the displayed isomorphism.
No boundedness is required, and the zero ring is included.
(blueprint: lem-pc-affine-module-complex-representative). -/
theorem exists_affine_module_complex_representative (Y : Scheme.{u}) [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory Y) (hE : schemeDerivedQCohProperty Y E) :
    ∃ M : CochainComplex (ModuleCat.{u} Γ(Y, ⊤)) ℤ,
      Nonempty (E ≅ DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings Y.toRingedSpace))
            (Scheme.Modules.restrictFunctor Y.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor Y.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(Y, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace))
                (tilde.functor Γ(Y, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M))) := by
  classical
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Y, ⊤))
  let F : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace) :=
    Scheme.Modules.restrictFunctor Y.isoSpec.inv
  let G : SheafOfModules.{u} (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
    Scheme.Modules.restrictFunctor Y.toSpecΓ
  let : F.Additive := by
    change (Scheme.Modules.restrictFunctor Y.isoSpec.inv).Additive
    infer_instance
  let : G.Additive := by
    change (Scheme.Modules.restrictFunctor Y.toSpecΓ).Additive
    infer_instance
  let : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (Scheme.Modules.restrictFunctor Y.isoSpec.inv)
    infer_instance
  let : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (Scheme.Modules.restrictFunctor Y.isoSpec.inv)
    infer_instance
  let : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (Scheme.Modules.restrictFunctor Y.toSpecΓ)
    infer_instance
  let : PreservesFiniteColimits G := by
    change PreservesFiniteColimits (Scheme.Modules.restrictFunctor Y.toSpecΓ)
    infer_instance
  have eFG : F ⋙ G ≅ 𝟭 _ :=
    (Scheme.Modules.restrictFunctorComp Y.toSpecΓ Y.isoSpec.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by
        rw [← Scheme.isoSpec_hom]
        exact Y.isoSpec.hom_inv_id) ≪≫ Scheme.Modules.restrictFunctorId
  let eD : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso eFG ≪≫ Functor.mapDerivedCategoryIdIso _
  have hFE : schemeDerivedQCohProperty (Spec Γ(Y, ⊤)) (F.mapDerivedCategory.obj E) := by
    intro n
    let h := hE n
    let eH := (F.mapDerivedCategoryHomologyFunctorIso n).app E
    apply (SheafOfModules.isQuasicoherent
      (moduleRings (Spec Γ(Y, ⊤)).toRingedSpace)).prop_of_iso eH
    change ((Scheme.Modules.restrictFunctor Y.isoSpec.inv).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E)).IsQuasicoherent
    infer_instance
  obtain ⟨a, ⟨α⟩, _, _⟩ := exists_affineQCohDerivedEquivalence_core Γ(Y, ⊤)
  let K : schemeDerivedQCohCategory (Spec Γ(Y, ⊤)) := ⟨F.mapDerivedCategory.obj E, hFE⟩
  let D := a.inverse.obj K
  let M := DerivedCategory.Q.objPreimage D
  let β := a.functor.mapIso (DerivedCategory.Q.objObjPreimageIso D) ≪≫ a.counitIso.app K
  let γ := (schemeDerivedQCohProperty (Spec Γ(Y, ⊤))).ι.mapIso β.symm ≪≫ α.app M
  refine ⟨M, ⟨(eD.app E).symm ≪≫ G.mapDerivedCategory.mapIso γ ≪≫ ?_⟩⟩
  exact G.mapDerivedCategoryFactors.app _

end AlgebraicGeometry
