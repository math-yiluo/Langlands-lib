# Selecting a projective frame from a configuration with sparse hyperplane sections

This internal linear-algebra support unit selects a projective frame from a
finite configuration. It works over a field `K` with a vector space `V`. The
configuration is an indexed family `v : I → V` over a finite type `I`. It
uses the Library predicate `HyperplaneBound v q` from
`Langlands.AbelianScheme.PolarizedFiniteLevel.FiniteConfiguration`. That
predicate says that the kernel of every nonzero linear functional contains at
most `q` entries of the family, counted with their indices.

## Declarations

`span_snoc_omit_eq_top` fixes a basis `β : Fin (m + 1) → V` and a vector
`w` all of whose `β`-coordinates are nonzero. It forms the family of
`m + 2` vectors `Fin.snoc β w`, that is `β 0, …, β m, w`. For every index
`k : Fin (m + 2)`, the `m + 1` vectors left after omitting index `k` span
`V`.

`HyperplaneBound.exists_frame` assumes the following:

- `V` is finite-dimensional with `finrank K V = m + 1`;
- the family satisfies `HyperplaneBound v q`;
- `(m + 1) * q < card I`.

It produces indices `ρ : Fin (m + 2) → I` such that, for every `k`, the
family `j ↦ v (ρ j)` over the indices `j ≠ k` is linearly independent. In
projective terms, the `m + 2` points `[v (ρ j)]` form a projective frame:
any `m + 1` of them are in general position.

## Proofs

For `span_snoc_omit_eq_top`, the proof uses `Fin.lastCases` on `k`. If `k`
is the last index, the remaining vectors are exactly the basis. If `k` is
the image of a basis index `i₀`, every basis vector other than `β i₀`
remains, and so does `w`. Expanding `w` in the basis and subtracting the
other basis terms shows that `β.repr w i₀ • β i₀` lies in the span. This
coefficient is nonzero by hypothesis, so `β i₀` lies in the span.

For `HyperplaneBound.exists_frame`, the bound with `q < card I`
(Library `HyperplaneBound.span_eq_top`) shows that the family spans `V`.
Mathlib's `exists_linearIndependent'` extracts a linearly independent
subfamily with the same span. Its index type has `m + 1` elements, so after
reindexing by `Fin (m + 1)` it is a basis `β` of entries `v (σ i)`. The
`m + 1` coordinate functionals of `β` are nonzero. The Library union bound
`HyperplaneBound.exists_avoiding` uses `(m + 1) * q < card I` to give an
index `i₀` whose entry has every `β`-coordinate nonzero. The frame is
`ρ = Fin.snoc σ i₀`. For each `k`, the remaining `m + 1` entries span by
`span_snoc_omit_eq_top`. Since their number equals the dimension, Mathlib's
`linearIndependent_of_top_le_span_of_card_eq_finrank` makes them linearly
independent.

## Provenance

This is an internal deduction from Mathlib's basis extraction, the
spanning-and-cardinality criterion for linear independence, and the Library
union bound for `HyperplaneBound`. It isolates the frame-choice step behind
the chart construction in Mumford, Fogarty and Kirwan, *Geometric Invariant
Theory*, third edition (1994). There the hyperplane estimate for torsion
points (Proposition 7.7, printed pp.138–139 / one-based PDF pp.151–152) is
used to show that the configuration of torsion points is stable. This unit
proves only the linear-algebra selection over a field. It says nothing about
abelian varieties, torsion points or moduli.
