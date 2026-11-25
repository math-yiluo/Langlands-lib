/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.Compactification.ValuativeCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Valuation probes at closure points of a quasi-compact immersion

Source: Stacks Project, Morphisms, Lemma 29.6.5, Tag 02JQ
(blueprint: lem-sc-picard-valuation-probe-closure).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every point in the closure of the image of a quasi-compact immersion is the centre
of a valuative commutative square. The square carries a valuation ring `sq.R`, its
fraction field `sq.K`, a map `sq.i₂ : Spec sq.R ⟶ S`, and a map `sq.i₁ : Spec sq.K ⟶ Z`.
Its commutativity says that the generic restriction of `sq.i₂` equals `sq.i₁ ≫ j`.
Source: Stacks Project, Morphisms, Lemma 29.6.5, Tag 02JQ
(blueprint: lem-sc-picard-valuation-probe-closure).

Proof:
1. Apply `exists_specializes_of_mem_closure_range` to `j` and `hs`
(`lem-sc-picard-closure-specialization`). Quasi-compactness gives a point `z : Z`
whose image specializes to `s`.
2. Apply `ValuativeCommSqWithPt.ofSpecializes` to this specialization
(`lem-sc-picard-valuation-probe-specializes`). It constructs the valuation square
from a valuation subring of the residue field at `z` dominating the image of the
stalk at `s`. Its `closedPoint_eq` identifies the image of the closed point with `s`.
3. Forget the bundled centre equation and return the underlying square together with
that equation. No additional assumption on residue fields is needed. -/
theorem exists_valuativeCommSq_of_mem_closure_range
    {Z S : Scheme.{u}} (j : Z ⟶ S) [QuasiCompact j] [IsImmersion j]
    {s : S} (hs : s ∈ closure (Set.range j)) :
    ∃ sq : ValuativeCommSq j, sq.i₂ (IsLocalRing.closedPoint sq.R) = s := by
  obtain ⟨z, hz⟩ := exists_specializes_of_mem_closure_range j hs
  let sq := ValuativeCommSqWithPt.ofSpecializes j hz
  exact ⟨sq.toValuativeCommSq, sq.closedPoint_eq⟩

end AlgebraicGeometry
