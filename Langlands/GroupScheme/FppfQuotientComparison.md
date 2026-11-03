# Base change and uniqueness of fppf kernel quotients

This derived helper concerns supplied actual group-scheme homomorphisms and the
published `RelativeRoot.IsFppfQuotient` predicate. It does not construct a
quotient of an arbitrary normal subgroup.

`kernel_range_baseChange` proves that the full all-test range of the actual
scheme kernel commutes with every change of base. A point is in the kernel
exactly when its composite is one. The base-change point equivalence preserves
composition and one, proving the equality on all tests.

`RelativeRoot.IsFppfQuotient.baseChange` preserves the quotient predicate under
any change of base. Flatness, surjectivity and local finite presentation are
stable under base change, and the preceding full-kernel equality supplies the
remaining condition.

For two supplied fppf quotients `q : G → Q` and `r : G → R` of the same subgroup
functor, `FppfQuotientComparison.hom` is their canonical comparison map, assuming
`q` quasi-compact. The kernel equality says that `r` kills the whole kernel of
`q`, so the Library's fpqc homomorphism descent constructs this map.
`fac` proves that its composite with `q` is `r`. Maps out of a quotient are
determined on `G`, because a flat surjective morphism is an epimorphism.
When both quotient maps are quasi-compact, the comparisons in both directions
are inverse. `FppfQuotientComparison.iso` is this actual isomorphism, `iso_fac`
is its defining common-source equation, and `iso_unique` proves uniqueness.

The construction works over any scheme base in universe `u`; it imposes no
smoothness, reducedness, normality, characteristic or field hypothesis. It is
derived from the published kernel point correspondence, base-change point
equivalence, stability of the three fppf morphism properties, and
`FpqcHomDescent.hom` with its factorization and uniqueness properties.
