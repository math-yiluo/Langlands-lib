/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatTraceDiscriminantGluing
import WeilConjectures.AlgebraicGeometry.Morphisms.TraceDiscriminantFibreEtaleCriterion

/-!
# The locally principal branch locus of a finite flat morphism

## References

* Stacks Project, Tag 0BVH
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The discriminant ideal cuts out exactly the image of the non-etale locus. -/
theorem exists_locallyPrincipal_branch_ideal_of_finite_flat
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] :
    ∃ J : Y.IdealSheafData, J.IsLocallyPrincipal ∧
      ∀ y : Y, y ∈ J.support ↔
        ∃ x : X, f x = y ∧ ¬ (∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f)) := by
  obtain ⟨J, hJ⟩ := exists_ideal_locally_eq_trace_discriminant_of_finite_flat f
  refine ⟨J, ?_, ?_⟩
  · intro y
    obtain ⟨U, hy, n, b, hb⟩ := hJ y
    refine ⟨U, hy, ?_⟩
    rw [hb]
    exact ⟨_, rfl⟩
  · intro y
    obtain ⟨U, hy, n, b, hb⟩ := hJ y
    rw [IdealSheafData.mem_support_iff_of_mem hy, hb, Y.zeroLocus_span]
    exact trace_discriminant_zeroLocus_iff_nonEtale_fibre f U y hy n b

end AlgebraicGeometry.Scheme
