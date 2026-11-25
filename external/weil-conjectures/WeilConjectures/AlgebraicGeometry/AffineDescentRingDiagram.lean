/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Modules.Tilde
/-! # Canonical coordinate-ring diagrams for affine descent

Source: Stacks Project, Tag 09RF, affine case.
(blueprint: def-pc-affine-descent-ring-diagram).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
variable {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (i : I)
variable {Z : Scheme.{u}} (t : Z ⟶ Spec (R.obj i))
/-- The base change at an index on the tail above `i`.
Source: Stacks Project, Tag 09RF, affine case
(blueprint: def-pc-affine-descent-ring-diagram). -/
noncomputable def affineDescentStage (j : Set.Ici i) : Scheme.{u} :=
  pullback t (Spec.map (R.map (homOfLE j.property)))
/-- The canonical transition morphism of base changes.
Source: Stacks Project, Tag 09RF, affine case
(blueprint: def-pc-affine-descent-ring-diagram). -/
noncomputable def affineDescentTransition {j k : Set.Ici i} (h : j ≤ k) :
    affineDescentStage R i t k ⟶ affineDescentStage R i t j :=
  baseChangeMap t
    (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
    (T' := Over.mk (Spec.map (R.map (homOfLE k.property))))
    (Over.homMk (Spec.map (R.map (homOfLE h)))
    (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
/-- The global-ring diagram of the actual tail base changes.
Source: Stacks Project, Tag 09RF, affine case
(blueprint: def-pc-affine-descent-ring-diagram). -/
noncomputable def affineDescentRings : Set.Ici i ⥤ CommRingCat.{u} where
  obj j := Γ(affineDescentStage R i t j, ⊤)
  map f := (affineDescentTransition R i t (leOfHom f)).appTop
  map_id j := by
    have h : affineDescentTransition R i t (le_refl j) = 𝟙 _ := by
      unfold affineDescentTransition
      unfold affineDescentStage
      apply pullback.hom_ext <;> simp [baseChangeMap]
    simp [h]
  map_comp f g := by
    have h : affineDescentTransition R i t (leOfHom (f ≫ g)) =
        affineDescentTransition R i t (leOfHom g) ≫
          affineDescentTransition R i t (leOfHom f) := by
      unfold affineDescentTransition
      rw [← baseChangeMap_comp]
      congr 1
      apply Over.OverMorphism.ext
      change Spec.map (R.map _) = Spec.map (R.map _) ≫ Spec.map (R.map _)
      rw [← Spec.map_comp, ← R.map_comp]
      rfl
    simp [h]
variable (c : Cocone R)
/-- The canonical map from the limit base change to a tail stage.
Source: Stacks Project, Tag 09RF, affine case
(blueprint: def-pc-affine-descent-ring-diagram). -/
noncomputable def affineDescentLimitMap (j : Set.Ici i) :
    pullback t (Spec.map (c.ι.app i)) ⟶ affineDescentStage R i t j :=
  baseChangeMap t
    (T := Over.mk (Spec.map (R.map (homOfLE j.property))))
    (T' := Over.mk (Spec.map (c.ι.app i)))
    (Over.homMk (Spec.map (c.ι.app j.val))
    (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.property)]))
/-- The cocone of global rings of the canonical limit base-change maps.
Source: Stacks Project, Tag 09RF, affine case
(blueprint: def-pc-affine-descent-ring-diagram). -/
noncomputable def affineDescentRingCocone : Cocone (affineDescentRings R i t) where
  pt := Γ(pullback t (Spec.map (c.ι.app i)), ⊤)
  ι :=
    { app j := (affineDescentLimitMap R i t c j).appTop
      naturality {j k} f := by
        have h : affineDescentLimitMap R i t c k ≫
            affineDescentTransition R i t (leOfHom f) = affineDescentLimitMap R i t c j := by
          unfold affineDescentLimitMap affineDescentTransition
          rw [← baseChangeMap_comp]
          congr 1
          apply Over.OverMorphism.ext
          change Spec.map (c.ι.app k.val) ≫ Spec.map (R.map _) = Spec.map (c.ι.app j.val)
          rw [← Spec.map_comp, c.w (homOfLE (leOfHom f))]
        simpa [affineDescentRings] using congrArg Scheme.Hom.appTop h }
/-- Sheafification through the morphism to the spectrum of the given ring.
Source: Stacks Project, Tags 09RF and 06Z0
(blueprint: def-pc-affine-descent-ring-diagram). -/
noncomputable def affineDescentSheafification (Y : Scheme.{u}) (A : CommRingCat.{u})
    (r : A ⟶ Γ(Y, ⊤)) : ModuleCat.{u} A ⥤ Y.Modules :=
  tilde.functor A ⋙ Scheme.Modules.pullback (Y.toSpecΓ ≫ Spec.map r)

/-- (blueprint: def-pc-affine-descent-ring-diagram) -/
instance affineDescentSheafification_preservesZeroMorphisms
    (Y : Scheme.{u}) (A : CommRingCat.{u}) (r : A ⟶ Γ(Y, ⊤)) :
    (affineDescentSheafification Y A r).PreservesZeroMorphisms := by
  let : (tilde.functor A).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  unfold affineDescentSheafification
  infer_instance

/-- The derived object of the actual termwise associated-sheaf complex.
Source: Stacks Project, Tags 09RF and 06Z0
(blueprint: def-pc-affine-descent-ring-diagram). -/
noncomputable def affineDescentRealization (Y : Scheme.{u}) (A : CommRingCat.{u})
    (r : A ⟶ Γ(Y, ⊤))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ schemeDerivedCategory Y := by
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  exact (affineDescentSheafification Y A r).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

end AlgebraicGeometry
