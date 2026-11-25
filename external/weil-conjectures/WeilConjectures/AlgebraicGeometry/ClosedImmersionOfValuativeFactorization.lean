/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.AlgebraicGeometry.ValuativeSquareOfMemClosureRange
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Closedness of an immersion from valuative factorization

Source: Stacks Project, Morphisms, Tags 02JQ and 01R8, and Schemes, Tag 01IQ
(blueprint: lem-sc-picard-locus-closed-valuation-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-compact immersion whose valuation-ring maps factor whenever their generic
restrictions factor has closed image and is a closed immersion.
Source: Stacks Project, Tags 02JQ, 01R8 and 01IQ
(blueprint: lem-sc-picard-locus-closed-valuation-criterion).

The hypothesis is expressed using `ValuativeCommSq`: its generic map witnesses the
factorization of the restriction of its bottom map. Only factorization of the bottom
map is required, without an additional compatibility condition on its factorization.

Proof:
1. For a point of the closure of the image, obtain a valuation probe whose closed point
maps to it and whose generic restriction factors through `j`, by Tag 02JQ together with
Tag 01R8 (`lem-sc-picard-valuation-probe-closure`).
2. Apply the hypothesis to the probe. Its bottom map factors through `j`, so its closed
point has image in the range of `j`. Every point of the closure is therefore in the range,
and the range is closed.
3. An immersion with closed image is a closed immersion by Tag 01IQ
(`lem-weil-pbc-immersion-closed-image-closed-immersion`). -/
theorem isClosed_range_and_isClosedImmersion_of_valuativeFactorization
    {Z S : Scheme.{u}} (j : Z ⟶ S) [QuasiCompact j] [IsImmersion j]
    (h : ∀ sq : ValuativeCommSq j,
      ∃ l : Spec (CommRingCat.of sq.R) ⟶ Z, l ≫ j = sq.i₂) :
    IsClosed (Set.range j) ∧ IsClosedImmersion j := by
  have hclosed : IsClosed (Set.range j) := by
    apply isClosed_of_closure_subset
    intro s hs
    obtain ⟨sq, hsq⟩ := exists_valuativeCommSq_of_mem_closure_range j hs
    obtain ⟨l, hl⟩ := h sq
    refine ⟨l (IsLocalRing.closedPoint sq.R), ?_⟩
    rw [← Scheme.Hom.comp_apply, hl, hsq]
  exact ⟨hclosed, IsClosedImmersion.of_isPreimmersion j hclosed⟩

end AlgebraicGeometry
