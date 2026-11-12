# The maximal positive-part argument in Langlands exhaustion

This internal construction and its lemmas supply the norm argument used in
Renard VII.4.2(iii), printed p.244 / PDF p.250. They concern a supplied
family of vectors in a real inner product space. They do not construct the
actual Jacquet exponents, Langlands decomposition, or tempered representation.

## Construction

`maximalPositiveProjectionIndex s hs positive` chooses an original index
in a nonempty finite set `s` at which the norm of `positive` is maximal.
`norm_le_maximalPositiveProjectionIndex` gives the bound for every member
of `s`. The index universe and vector-space universe are independent.
The construction uses `Finset.exists_max_image` and classical choice.

## Implemented norm argument

Let `C` be a subset of a real inner product space, let `μ ∈ C`, and suppose
`λ` is orthogonal to `μ`. Suppose a proposed positive part `p` of `λ + μ`
has residual in the negative polar of `C`:

`∀ c ∈ C, inner ℝ (λ + μ - p) c ≤ 0`.

If `‖p‖ ≤ ‖μ‖`, then `positivePart_eq_of_norm_le` proves `p = μ`.
Indeed, testing the residual inequality at `μ` gives
`‖μ‖² ≤ inner ℝ p μ`. Expanding `‖p - μ‖²` and using the norm bound
therefore makes that nonnegative square at most zero. Thus `p = μ`.
Substitution shows that `λ` itself has nonpositive inner product with
every member of `C`, which is the conclusion of
`nonpositive_inner_of_maximal_positivePart`.

`nonpositive_inner_of_maximalPositiveProjectionIndex` combines this
argument with the finite selection. For a member `j`, its vector is
`parameter j`, its proposed positive part is `positive j`, and `μ` is the
selected maximal positive part. The supplied orthogonality condition is
between `parameter j - μ` and `μ`; the supplied residual condition concerns
`parameter j - positive j`. The theorem proves both `positive j = μ` and
that `parameter j - μ` belongs to the negative polar.

No finite dimension, completeness, convexity, or closedness is required for
these implications: the residual inequality is an explicit hypothesis.
For a closed convex cone it is the normal-cone condition supplied by the
orthogonal cone decomposition. The file asserts no projection existence.

## Provenance and retained obligations

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VII.4.2(iii), printed
pp.243–244 / PDF pp.249–250. Renard selects `μ` to maximize the norm of its
positive part, then uses orthogonal decompositions and distance inequalities
to force each twisted exponent into the negative cone. The implemented
argument uses the same maximality and orthogonality but a shorter
inner-product calculation with the polar residual. This is an internal
derivation, not a claim to reproduce the printed sequence of inequalities.

An application to the classification still has to supply the nonempty
finite family of actual exponents, remove and identify the actual central
directions, obtain the positive parts and polar residuals from V.3.18,
prove orthogonality and occurrence of the twisted exponents, identify the
negative polar with the required actual root cone, and apply the tempered
criterion. None of these structural or representation-theoretic assertions,
nor the full exhaustion statement, is proved here.
