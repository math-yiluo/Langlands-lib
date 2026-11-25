/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.ModuleCupNaiveMap
import WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackMatesIsIso
/-! # Tensor-counit normalization of the global pullback

Source: Stacks Tags 008A, 008Y, 0B6A and 0FKU. -/

@[expose] public section
universe u
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable (X : Scheme.{u})
local instance globalPullbackOplaxCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))
local instance globalPullbackOplaxMonoidal :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.toRingedSpace.sheaf
local instance globalPullbackOplaxSymmetric :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.toRingedSpace.sheaf
attribute [local instance] globalPullbackMatesColimits
local instance globalPullbackOplaxPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).1
local instance globalPullbackOplaxClosed :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.toRingedSpace.sheaf).2.1
/-- The mate isomorphisms coincide with the explicit oplax structure transported
from the adjunction.
Source: Mathlib.CategoryTheory.Monoidal.Functor, Adjunction.leftAdjointOplaxMonoidal.
(blueprint: lem-sc-global-tensor-pullback-oplax-isiso)
Proof: unfold the transported oplax unit and tensor maps, rewrite them using
the prescribed concrete lax unit and tensor maps, and apply the isomorphism
assertions for the corresponding adjunction mates. -/
theorem globalTensorPullback_oplax_isIso
    (P : ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (adj : P ⊣ RingedSpace.globalSectionsFunctor X.toRingedSpace)
    (lax : (RingedSpace.globalSectionsFunctor X.toRingedSpace).LaxMonoidal)
    (hε : Functor.LaxMonoidal.ε (RingedSpace.globalSectionsFunctor X.toRingedSpace) =
      ModuleCat.ofHom (unitSectionsEquiv (X := X) ⊤).toLinearMap)
    (hμ : ∀ M N, Functor.LaxMonoidal.μ (RingedSpace.globalSectionsFunctor X.toRingedSpace) M N =
      moduleCup_sectionTensorMap X M N) :
    IsIso (adj.leftAdjointOplaxMonoidal.η) ∧
      (∀ A B, IsIso (adj.leftAdjointOplaxMonoidal.δ A B)) := by
  obtain ⟨hunit, htensor⟩ := globalTensorPullback_mates_isIso X P adj
  constructor
  · change IsIso ((adj.homEquiv _ _).symm
      (Functor.LaxMonoidal.ε (RingedSpace.globalSectionsFunctor X.toRingedSpace)))
    rw [hε]
    exact hunit
  · intro A B
    change IsIso ((adj.homEquiv _ _).symm
      ((adj.unit.app A ⊗ₘ adj.unit.app B) ≫
        Functor.LaxMonoidal.μ (RingedSpace.globalSectionsFunctor X.toRingedSpace) _ _))
    rw [hμ]
    exact htensor A B

end
end AlgebraicGeometry.Scheme.Modules
