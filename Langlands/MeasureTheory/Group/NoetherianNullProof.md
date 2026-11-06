# Noetherian induction for null closed inverse images

Authors: Worker 1650 and Worker 135.

`noetherianClosedNull` implements the internal measure argument in
`NoetherianClosedNullStatement`. The hypotheses and both universes are
unchanged.

Induct on closed subsets of the Noetherian space. If the inverse image of a
proper closed set `Z` has positive measure, inner regularity supplies a
compact subset `K` of positive measure. Compactness and the Hausdorff
property make `K` closed. The published Mathlib theorem
`eventually_nhds_one_measure_smul_sdiff_lt` gives an identity neighborhood on
which `μ (g • K \ K) < μ K`.

Choose `x ∈ K`. The empty-interior hypothesis makes the complement of
`f ⁻¹' Z` dense. Continuity of `y ↦ x * y⁻¹` therefore gives `y` in that
complement for which `g = x * y⁻¹` is sufficiently close to the identity.
Since `g * y = x`, equivariance implies that `f x` belongs to `Z` but not to
the translate `T = (e g).symm ⁻¹' Z`. Thus `Z ∩ T` is strictly smaller than
`Z` and remains proper.

The inductive hypothesis makes the inverse image of `Z ∩ T` null.
Equivariance puts `g • K ∩ K` inside this inverse image. Decomposing
`g • K` into its intersection with `K` and its difference from `K`, and
using left invariance, now gives `μ K = μ (g • K \ K)`. This contradicts
the chosen strict inequality.

The proof requires no dimension theory, algebraic stabilizer, right
invariance, or integration formula. This module supplies only the generic
theorem; actual rational-point applications must discharge all its
topological and measure hypotheses separately.
