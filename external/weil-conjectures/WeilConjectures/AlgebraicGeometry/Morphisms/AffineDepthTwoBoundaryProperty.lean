/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import WeilConjectures.RingTheory.Depth
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Dual.Defs

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.RingTheory.DualDepthTwo
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineDoubleDualStalk

/-! # Depth two of the finite double dual at boundary points

## References

* Stacks Project, Tags 0EY6, 0583 and the local Hom-depth bound 0AV5(2)
-/

@[expose] public section
universe u v w
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme
-- Transport depth while enlarging the ideal; equality of ideals is not required.
private theorem ideal_depth_le_of_equiv_of_le {R : Type u} [CommRing R]
    (I J : Ideal R) (hIJ : I ≤ J)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (e : M ≃ₗ[R] P) : I.depth M ≤ J.depth P := by
  have hmap : (I • (⊤ : Submodule R M)).map e.toLinearMap =
      I • (⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  unfold Ideal.depth
  split_ifs with hM hP hP
  · exact le_rfl
  · have hIP : I • (⊤ : Submodule R P) = ⊤ := by
      rw [← hmap, hM]
      simp
    have hle : I • (⊤ : Submodule R P) ≤ J • (⊤ : Submodule R P) :=
      Submodule.smul_mono hIJ le_rfl
    rw [hIP] at hle
    exact (hP (top_unique hle)).elim
  · exact le_top
  · apply sSup_le_sSup
    rintro n ⟨rs, hreg, hmem, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).mp hreg,
      fun x hx => hIJ (hmem x hx), rfl⟩

/-- The sheaf of the actual finite double dual has depth two at boundary points. -/
theorem affine_depth_two_boundary_property
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (hboundary : ∀ x : Spec A, x ∉ W →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec A).presheaf.stalk x) ((Spec A).presheaf.stalk x))
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    ∀ x : Spec A, x ∉ W →
      ∃ hfinite : Module.Finite ((Spec A).presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u})
            (tilde (ModuleCat.of A (Module.Dual A (Module.Dual A M)))).val.presheaf x),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := (Spec A).presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u})
            (tilde (ModuleCat.of A (Module.Dual A (Module.Dual A M)))).val.presheaf x) := by
  intro x hx
  obtain ⟨hfinite, ⟨e⟩⟩ := affine_double_dual_stalk A M x
  let R := (Spec A).presheaf.stalk x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) (tilde M).val.presheaf x
  have : Module.Finite R N := hfinite
  have hfin : Module.Finite R
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (tilde (ModuleCat.of A (Module.Dual A (Module.Dual A M)))).val.presheaf x) :=
    Module.Finite.equiv e.symm
  refine ⟨hfin, ?_⟩
  apply le_trans (IsLocalRing.dual_depth_ge_two R (Module.Dual R N) (hboundary x hx))
  exact ideal_depth_le_of_equiv_of_le (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal R) le_rfl e.symm

end AlgebraicGeometry.Scheme
