/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound

/-!
# Openness of the bounded local fibre dimension locus

## References

* Stacks Project, Morphisms, Tag 02FZ
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a locally finite type morphism, the points with local fibre dimension at most `n`
form an open subset of the source. The point `f.asFiber x` is the unique point of
`f.fiber (f x)` mapping to `x`. No properness, quasi-compactness, Noetherian,
finite-presentation, or flatness hypothesis is imposed. -/
theorem isOpen_localFibreDimension_le {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (n : ℕ) :
    IsOpen {x : X | topologicalKrullDimAt (f.asFiber x) ≤ (n : WithBot ℕ∞)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hfinite : ∃ d : ℕ,
      topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞) := by
    have hnonneg : 0 ≤ topologicalKrullDimAt (f.asFiber x) := by
      refine le_iInf₂ fun U hxU ↦ ?_
      apply Order.krullDim_nonneg_iff.mpr
      exact ⟨⟨closure {⟨f.asFiber x, hxU⟩}, isIrreducible_singleton.closure,
        isClosed_closure⟩⟩
    have hle : topologicalKrullDimAt (f.asFiber x) ≤ (n : WithBot ℕ∞) := hx
    generalize topologicalKrullDimAt (f.asFiber x) = e at hle hnonneg ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact False.elim ((not_le_of_gt (by decide : (⊥ : WithBot ℕ∞) < 0)) hnonneg)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exact False.elim ((not_le_of_gt
          (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n))) hle)
      | coe e => exact ⟨e, rfl⟩
  obtain ⟨d, hd⟩ := hfinite
  obtain ⟨W, hxW, hW⟩ := exists_bounded_fibre_dimension_neighbourhood f x d hd
  refine mem_nhds_iff.mpr ⟨W, ?_, W.isOpen, hxW⟩
  intro y hy
  have hdn : (d : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    exact hd ▸ hx
  exact (hW y hy).trans hdn

end AlgebraicGeometry
