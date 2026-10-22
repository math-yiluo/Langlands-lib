# The cyclic degree-two cocycle-sum comparison

The companion Lean file defines the proposition
`Langlands.Cohomology.CyclicH2.CocycleSumComparison.{u}`. It supplies a statement
for a later proof; it does not prove the comparison.

## Exact statement

Let `k` and `G` belong to `Type u`, with `k` a commutative ring and `G` a
commutative group equipped with a `Fintype` instance. Let `A : Rep k G`, and let
`g : G` satisfy `hg : ∀ y, y ∈ Subgroup.zpowers g`, so that `g` generates `G`.
Write `n = Fintype.card G`, and let `ρ` be the action on `A`.

For every arbitrary two-cocycle `c : groupCohomology.cocycles₂ A` and every
element `x` of `ker(ρ(g) − id)`, the equality

\[
  x=\sum_{i=0}^{n-1}c(g^i,g)
\]

in the underlying module implies

\[
  \operatorname{H2\pi}_A(c)
  =\operatorname{groupCohomology\pi Even}_{A,g,hg,2}(x)
  \quad\text{in }H^2(G,A).
\]

The left side is Mathlib's quotient map from inhomogeneous two-cocycles.
The right side is exactly
`Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by decide)`.
This map takes a kernel element to its class modulo the norm image and then
uses the inverse of Mathlib's `groupCohomologyIsoEven`. That isomorphism uses
Mathlib's `groupCohomologyIso`, defined through its Ext comparison and the
finite cyclic projective resolution.

All quantifiers and hypotheses are inside the single Prop-valued definition.
There is no assumption identifying an unspecified comparison with this map.
No field, characteristic, invertibility-of-order, or nontriviality assumption
is made. In particular, groups of order one are included. The cocycle need not
vanish when one argument is the identity: the sum includes the term
`c (1, g)`. The proposition is conditional on a supplied kernel element equal
to the sum; it does not separately assert that such an element exists.

## Provenance and conventions

The source convention is Jean-Pierre Serre, *Local Fields*, English translation
by Marvin Jay Greenberg, Springer, 1979, Chapter VIII, §4, Proposition 6,
its corollary, and the generator-character remark, printed pages 132–133
(PDF pages 138–139). Serre uses `D = g − 1` and
`N = 1 + g + ··· + g^(n−1)` in the periodic complex. In positive even degree
this gives `ker(D)/im(N)`, and the remark relates the generator-dependent
degree-two identification to the character taking `g` to `1/n` in `ℚ/ℤ`.
Serre formulates this for abelian group modules; the present statement uses
the same complexes for representations over an arbitrary commutative ring.

The explicit cocycle sum and its equality with Mathlib's fixed map are an
internal chain-level refinement, not a verbatim theorem of Serre. The intended
derivation uses a comparison from the cyclic resolution to the unnormalized
bar resolution whose values on the free generators in degrees zero, one, and
two are respectively

\[
  [],\qquad [g],\qquad \sum_{i=0}^{n-1}[g^i\mid g].
\]

With the bar differential
`d[a|b] = a[b] − [ab] + [a]`, the boundary of the degree-two value is
`N[g]`: the remaining terms telescope, using `g^n = 1`. The degree-one
boundary is `(g − 1)[]`, and the augmentation is the identity. Evaluating a
two-cocycle on the degree-two value yields precisely the displayed sum, with
the positive sign. This explains the proposed formula, including its
unnormalized convention. A later proof must establish the required comparison
and show that its induced map agrees with Mathlib's actual Ext-based
comparison. No such proof or agreement hypothesis is supplied here.

Registered source: `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The cited original pages were read for this statement.

## Formal dependencies and authorship

The only direct import is
`Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic`.
The relevant declarations are `groupCohomology.cocycles₂`,
`groupCohomology.H2π`, `Rep.applyAsHom`,
`Rep.FiniteCyclicGroup.groupCohomologyIsoEven`, and
`Rep.FiniteCyclicGroup.groupCohomologyπEven`.
The checked Mathlib revision is
`5ed2965256430c3649e86755f9576b54eca72435`, with Lean 4.34.0.
No project Library module is changed or required by this pair.

Worker 28 supplied the exact Lean interface and the chain-comparison design.
Worker 25 prepared this paired statement, checked the source conventions and
formal dependencies, and expanded the documentation.
