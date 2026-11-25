/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Local dimension of affine finite-type fibres

The affine finite-type fibre has finite local dimension.

## References

* Stacks Project, Tag 00QE
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The local dimension of a fibre of an affine locally finitely presented morphism is
represented by a natural number. -/
theorem exists_fiber_dimension_nat
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f] (y : X) :
    ∃ n : ℕ, topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hfinite := topologicalKrullDim_ne_top_of_compactSpace
    (f.fiberToSpecResidueField (f y))
  have hle : topologicalKrullDimAt (f.asFiber y) ≤
      topologicalKrullDim (f.fiber (f y)) := by
    exact (iInf₂_le ⊤ trivial).trans
      (topologicalKrullDim_subspace_le _ Set.univ)
  have hnonneg : (0 : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber y) := by
    refine le_iInf₂ fun (U : (f.fiber (f y)).Opens) hy ↦ ?_
    apply Order.krullDim_nonneg_iff.mpr
    exact ⟨⟨closure {⟨f.asFiber y, hy⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
    (ne_bot_of_le_ne_bot (by simp) hnonneg)
  have hdtop : d ≠ ⊤ := by
    intro heq
    apply hfinite
    apply top_le_iff.mp
    simpa [← hd, heq] using hle
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hdtop
  exact ⟨n, hd.symm⟩

end AlgebraicGeometry
