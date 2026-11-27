# The scheme center from dense rational points

`Langlands.GroupScheme.infiniteFieldCenterComparison` proves
[`InfiniteFieldCenterComparisonStatement`](InfiniteFieldCenterComparisonStatement.md):
for every infinite field \(k\) and every group scheme \(G\) over
\(\operatorname{Spec} k\) with `IsConnectedReductive G`,

```text
schemeCenterPoints G = Subgroup.center (rationalPoints G).
```

The left side is the full all-test center functor `center G` evaluated at
the identity test \(\operatorname{Spec} k\); membership requires that every
pullback of the point commutes with every point of \(G\) over every test
scheme, reduced or not. The right side is the abstract center of the group
\(G(k)\).

## The general criterion

`RationalCenterComparison.of_denseRationalPoints` proves the comparison for
any group scheme \(G\) over a field \(k\) whose underlying scheme is reduced,
whose structure morphism is separated, and whose rational points have
Zariski-dense images (`HasDenseRationalPoints k G.X`). It does not use that
\(k\) is infinite.

- The inclusion of the scheme center in the abstract center is
  `schemeCenterPoints_le_center`: evaluate the commutation law on the identity
  test.
- Conversely, let \(z \in G(k)\) be in the abstract center, so that \(z\) is
  a morphism \(z : \operatorname{Spec} k \to G\) over \(k\), and let
  \(t : G \to \operatorname{Spec} k\) be the terminal morphism. Then
  \(z \circ t : G \to G\) is a point of \(G\) with values in \(G\) itself
  (written `t ≫ z` in Lean). Consider the two morphisms \(G \to G\) given by
  left and right translation by \(z\), namely
  \((z \circ t)\cdot \mathrm{id}_G\) and \(\mathrm{id}_G \cdot (z \circ t)\)
  in the group of points \(G(G)\). Composed with a rational point
  \(p : \operatorname{Spec} k \to G\), they become \(z p\) and \(p z\),
  since \(t \circ p\) is the identity of the terminal test \(\operatorname{Spec} k\),
  so that \((z \circ t) \circ p = z\); these agree because \(z\) is central in
  \(G(k)\). The lemma
  `hom_ext_of_denseRationalPoints` (morphisms from a reduced scheme to a
  separated one agreeing on a dense union of images of rational points are
  equal) makes the two translations equal as morphisms over \(k\).
- For an arbitrary test \(T\), a morphism \(a : T \to \operatorname{Spec} k\)
  and a point \(g : T \to G\) in \(G(T)\), we have \(a = t \circ g\)
  (written `a = g ≫ t` in Lean), because \(\operatorname{Spec} k\) is terminal
  over itself. The pullback of \(z\) to \(T\) along \(a\) is the \(T\)-point
  \(z \circ a\) (written `a ≫ z` in Lean). Precomposing the equality of the
  two translations with \(g\), and using \((z \circ t) \circ g = z \circ a\),
  therefore gives \((z \circ a) \cdot g = g \cdot (z \circ a)\) in \(G(T)\).
  This holds for every test scheme
  \(T\), including nonreduced ones, since it is obtained from an equality of
  morphisms on \(G\) and not from an argument on points of \(T\).

## Connected reductive groups over infinite fields

For `IsConnectedReductive G`, the field `smooth` together with
`Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field`
shows that the underlying scheme of \(G\) is reduced, and the field
`isAffineHom` makes the structure morphism separated. The theorem
`reductiveRationalPointDensity`, which proves
`ReductiveRationalPointDensityStatement`, supplies the density of rational
points over every infinite field. The criterion then gives the equality of
the two subgroups of the same rational-point group. No hypothesis on the
characteristic, perfectness, splitting, or smoothness of the center is used.

## Relation to the literature

The statement's Markdown records the source: Milne, *Algebraic Groups*
(2017), Proposition 1.93 with \(H = G\) and \(k' = k\) (for a smooth
algebraic subgroup \(H\) with \(H(k')\) dense in \(H\), the \(k\)-points of
the centralizer are the elements of \(G(k)\) centralizing \(H(k')\)),
Proposition 1.92 for the center as the all-test centralizer, and
Theorem 17.93(b) for the density of \(G(k)\) over an infinite field.
Milne proves Proposition 1.93 through the normalizer and the subgroup on
which conjugation is the identity. The Lean proof instead compares the two
translations directly: density enters through
`reductiveRationalPointDensity`, and the separation argument is
`hom_ext_of_denseRationalPoints`, which shows that the scheme-theoretic
equalizer of the two translations is dominant and hence, \(G\) being
reduced and separated, that the translations are equal.
