/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

import WeilConjectures.AlgebraicGeometry.Morphisms.DepthOneRestrictionInjective
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoRestrictionBoundarySurjective
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Restriction and direct image of a depth-two module

## References

* Stacks Project, Lemma 31.5.11, Tag 0E9I
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Restriction followed by direct image recovers a coherent depth-two module. -/
theorem isIso_restrictAdjunction_unit_of_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) :
    IsIso ((Modules.restrictAdjunction U.ι).unit.app N)  := by
  classical
  let η := (Modules.restrictAdjunction U.ι).unit.app N
  have hdepth₁ : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (1 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y) := by
    intro y hy
    obtain ⟨hf, hd⟩ := hdepth y hy
    exact ⟨hf, le_trans (by norm_num) hd⟩
  have hinj := injective_restrictAdjunction_unit_app_of_depth_one U N hqc hsections hdepth₁
  have hstalk (y : L) : Function.Bijective
      ((stalkFunctor Ab.{u} y).map ((Modules.toPresheaf L).map η)) := by
    by_cases hy : y ∈ U
    · exact Modules.bijective_stalk_of_isIso_restrict η y hy
    · refine ⟨?_, surjective_restrictAdjunction_unit_stalk_of_depth_two
        U N hqc hsections hdepth hinj y hy⟩
      exact stalkFunctor_map_injective_of_app_injective (fun V ↦ hinj V) y
  rw [Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  exact app_bijective_of_stalkFunctor_map_bijective
    (F := ⟨N.presheaf, N.isSheaf⟩)
    (G := ⟨_, ((Modules.pushforward U.ι).obj (N.restrict U.ι)).isSheaf⟩)
    ⟨(Modules.toPresheaf L).map η⟩ V (fun y _ ↦ hstalk y)

end AlgebraicGeometry.Scheme
