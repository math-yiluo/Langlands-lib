# Affine-chart reduction for closed-point stalk dimension

`Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension_of_maximalHeight.{u}`
is an internal conditional adapter. Its explicit argument asserts that every
maximal ideal in a standard-smooth algebra of relative dimension `n` over any
field in universe `u` has height `n`. Given that argument, it proves exactly
`FieldSmoothClosedPointStalkDimensionStatement.{u}`. It does not independently
establish that algebraic argument and is intended as a helper module in the
single unconditional proof submission.

The implemented reduction starts with the affine chart furnished by Mathlib's
`SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`.
Its base open `U` contains the image of the chosen point. The spectrum of a
field is a singleton, so `U` is the entire base. The canonical ring equivalence
`Scheme.ΓSpecIso` makes its ring of global sections a field; the chart algebra
structure is exactly `(f.appLE ⊤ V e).hom.toAlgebra`, preserving the supplied
standard-smooth relative dimension. No change of scalar structure is required.

For the affine source neighborhood `V`, the point determines the ideal
`(hV.primeIdealOf ⟨x, hxV⟩).asIdeal`. Mathlib's
`IsAffineOpen.primeIdealOf_isMaximal_of_isClosed` uses the original closed-point
hypothesis to prove maximality. `IsAffineOpen.isLocalization_stalk` identifies
the actual ring `X.presheaf.stalk x` as the localization of `Γ(X,V)` at this
ideal. `IsLocalization.AtPrime.ringKrullDim_eq_height` then gives its Krull
dimension as the ideal height, cast from `ℕ∞` to `WithBot ℕ∞`. The explicit
algebraic argument gives height `g`, and applying the same cast proves the
published conclusion. Empty schemes need no special case because a point is
already fixed.

This reduction is derived internally from these pinned Mathlib results. It
retains arbitrary fields and arbitrary universe `u` and requires no global
finiteness, connectedness, regularity, or differential comparison. The published
statement pair and its import closure are unchanged.

The statement's retained provenance was checked in the registered source
`stacks-smooth-differential-rank-2026-10-22`, `01V4.html`, Lemma 29.35.12
(Tag 02G1), Definition 29.35.13 (02G2), and Lemma 29.35.8 (01VE), and source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, `varieties.tex`,
`lemma-dimension-locally-algebraic`, closed-point item (2) and its proof.
The implemented proof uses affine ideal height directly instead of the source's
intermediate local topological dimension and differential rank. Worker 399
authored this geometric adapter in coordination with Worker 669, who owns the
algebraic dimension argument and final theorem.
