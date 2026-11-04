# Pseudo-reductivity and reductivity over a perfect field

`PerfectFieldPseudoReductiveStatement` is the proposition that, for every
field `k` in an arbitrary universe `u`, with `[PerfectField k]`, and every
actual group scheme `G` over `Spec k`,

```text
IsPseudoReductive G ↔ IsConnectedReductive G.
```

Both predicates come from `Langlands.GroupScheme.Reductive.Basic`. Each
includes smoothness, affineness and connectedness of `G`. The left side
requires `HasTrivialUnipotentRadical G`, the published predicate saying that
every smooth connected unipotent normal closed subgroup over `k` has trivial
image on every test scheme. The right side requires that predicate for the
actual pullback of `G` along `toAlgebraicClosure k`. Thus the conclusion
compares the ground-field condition with geometric reductivity of the
same group scheme.

The statement assumes only perfectness of the field in addition to the
conditions contained in the two predicates. It imposes no splitness,
algebraic closedness, characteristic restriction, supplied radical or
radical base-change premise. Subgroup predicates and base change use the
Library's group objects in `Over (Spec k)` and all test schemes, including
nonreduced tests.

## Source and correspondence

B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second
edition (2015), source `conrad-gabber-prasad-2015-pseudo-reductive`,
Definition 1.1.1 on printed p. 3 and the opening paragraph on printed p. 4
(PDF pp. 29–30).

Definition 1.1.1 defines pseudo-reductivity for smooth connected affine
groups by triviality of the ground-field unipotent radical. The opening
paragraph of p. 4 states that, over a perfect field, pseudo-reductivity
and reductivity coincide: the ground-field radical after base change
equals the geometric unipotent radical. The Lean target expresses the
resulting equivalence directly through the published trivial-radical
predicates. It does not assert existence of a chosen radical or an
equality between chosen radical objects.

The implication from `IsConnectedReductive G` to `IsPseudoReductive G`
is already proved over arbitrary fields by
`IsConnectedReductive.isPseudoReductive` in
`Langlands.GroupScheme.Reductive.ToPseudoReductive`. The perfect-field
converse remains a proof obligation. This module declares a proposition
target and contains no proof of the equivalence.
