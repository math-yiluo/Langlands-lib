# Finite sampled-value Schwartz expansions

This module proves two generic finite pointwise expansions in
`Langlands.HarmonicAnalysis`, using the existing `SchwartzBruhat X` from
`Basic`. The space `X` and the arbitrary parameter type `A` have independent
universes.

`FiniteSchwartzExpansion H` bundles the finite size, Schwartz–Bruhat functions,
sample points, and their pointwise reconstruction identity for the whole family.
The noncomputable definition `finiteSchwartzExpansion H hH hC` chooses such
data using the proved existence theorem below. Its `expansion` field is a
proof of the reconstruction identity, so the constructor needs only the stated
local constancy and compact support hypotheses.

`exists_finite_schwartz_expansion` takes a map `H : X → A → ℂ` that is locally
constant as a map into the whole function space and has compact topological
support. It constructs a natural number `m`, Schwartz–Bruhat functions
`φ : Fin m → SchwartzBruhat X`, and representatives `r : Fin m → X`, before
quantifying over either `a` or `x`, such that
`H x a = ∑ i, φ i x * H (r i) a`. The domain needs only a topology.
There are no assumptions on the parameter type, including no topology,
finiteness, or inhabitance assumption.

The proof applies the published
`finite_range_of_locallyConstant_of_hasCompactSupport` from
`AlgebraicIntegrand` to the whole function-valued map. Its nonzero image is
finite. For each nonzero value the proof chooses a representative and takes
the characteristic function of its fiber. Local constancy is preserved under
arbitrary composition. The characteristic function vanishes at the zero
function, so its topological support is contained in that of `H`; it therefore
belongs to `SchwartzBruhat X`. When `H x = 0` all summands vanish. Otherwise
exactly the fiber of `H x` contributes, with sampled value equal to `H x`.
The finite index type of nonzero values is then reindexed by `Fin m`.
Empty support, empty parameter types, and empty domains require no separate
choices of a point outside a nonempty fiber; the resulting finite family can
be empty.

`exists_compactCosetExpansion` takes a Hausdorff topological additive
commutative group, an open additive subgroup `U`, a compactness witness for
`U`, and a family `H : A → X → ℂ`. Its hypotheses assert invariance under
translation by every element of `U` and the existence of one compact set
containing the nonzero support of every member of the family. Its conclusion
is the same finite identity in the order `H a x`, with all finite data chosen
before both variables.

To derive the corollary, the proof uses the open neighborhood
`{y | y - x ∈ U}` at each `x`. Invariance makes every coordinate of the
function-valued family constant on this one neighborhood, proving uniform
local constancy. Outside the supplied compact set, each coordinate is zero.
Hausdorffness then gives compact topological support of the whole family.
The general expansion applies. Compactness of `U` is retained in the
interface for compatibility and is not used by the proof. In particular,
the conclusion includes groups modeled on zero-dimensional spaces.

The constructed characteristic functions indicate disjoint nonzero fibers
of the whole family. In the subgroup application each fiber is a union of
`U`-cosets. The interface does not assert that each function indicates a
single coset, or that the zero-value portion of the supplied compact set is
covered. The identity holds at every point, including outside that set.
No measure, integral, or almost-everywhere identity is involved, and no
finite partition or expansion is assumed.

These are internal elementary consequences of local constancy and
compactness, rather than transcriptions of a separately sourced JPSS
theorem. The finite-range result is reused by its published Lean name; no
additional literature claim is made. Worker 180 authored the general
finite-expansion proof in the unreviewed revision-4 draft of task
`798cefd9-ab16-4562-ab1a-085680064306`, in
`Langlands.Representation.RankinSelberg.UnequalRankBlockSpanProof`.
Worker 451 adapted that proof to this generic module, preserving its independent
parameter universe, and authored the compact subgroup corollary and this
documentation, as well as the expansion data bundle and its constructor.
Both are actual coauthors of this unit. The adjacent-span
integration and representation arguments remain outside this module.
