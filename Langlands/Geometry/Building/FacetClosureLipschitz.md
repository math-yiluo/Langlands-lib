# Maps that are distance-nonincreasing on closed facets

Setting: a finite-dimensional real normed affine space `P` (a
`NormedAddTorsor V P` with `FiniteDimensional ℝ V`) and a set `Ψ` of affine
functionals on `P` which is locally finite in the sense of the `finite_bounded_at`
field of `AffineRootSystem.IsLocallyFiniteReflectionArrangement`: for each point
`x` and each bound `bound : V* → ℝ`, only finitely many `ψ ∈ Ψ` satisfy
`|ψ x| ≤ bound ψ.linear`. This hypothesis is stated directly, so the results
apply to any arrangement with that property. Closed facets are the Library's
`AffineRootSystem.facetClosure Ψ p`: the points `u` with `sign (ψ u) = 0` or
`sign (ψ u) = sign (ψ p)` for all `ψ ∈ Ψ`.

Results:

* `sign_eq_of_abs_sub_lt`: if `|u - v| < |v|` then `u` and `v` have the same
  sign;
* `abs_apply_sub_apply_le`: `|ψ y - ψ x| ≤ ‖ψ.linear‖ · dist y x`, with the
  operator norm of the linear part;
* `eventually_mem_facetClosure`: every point `x` lies in the closed facet of all
  sufficiently near points `y`. Only the finitely many `ψ` with
  `|ψ x| ≤ ‖ψ.linear‖` matter: for each of them with `ψ x ≠ 0`, `ψ y` keeps the
  sign of `ψ x` for `y` near `x`. Every other `ψ` keeps its sign on the unit ball
  around `x` by the Lipschitz estimate;
* `dist_le_of_forall_mem_facetClosure`: if `f : P → Q` into a pseudometric
  space satisfies `dist (f u) (f v) ≤ dist u v` whenever `u` and `v` lie in a
  common closed facet `facetClosure Ψ p`, then `dist (f a) (f b) ≤ dist a b`
  for all `a, b`.

This last statement is the segment-subdivision step of the proof of
Kaletha–Prasad (2023), Lemma 4.2.2(3), printed p.169 / PDF p.200: there, the
segment `[x, y]` is cut into finitely many pieces, each in the closure of one
facet, and the triangle inequality is summed. The Lean proof does not sort
crossing points. It parametrizes the segment by `t ↦ lineMap a b t` and proves
by continuous induction on `[0, 1]`
(`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`) that
`dist (f a) (f (lineMap a b t)) ≤ t · dist a b`. The step uses
`eventually_mem_facetClosure`: near `t`, the points `lineMap a b t` and
`lineMap a b s` share the closed facet of the latter. The same local estimate
makes `t ↦ f (lineMap a b t)` continuous, which gives the closedness needed for
the induction.

The local-finiteness hypothesis is the Library form of KP Axiom 4.1.6 /
Proposition 1.3.12, read with the corrections of 1 November 2024. The
statements are derived lemmas in the generality needed for the retraction
`ρ_{A,C}` on an apartment; no building is involved.

Author: Worker 1221.
