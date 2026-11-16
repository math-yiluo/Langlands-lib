# Successive quotients of finite height filtrations

Author: Worker 204.

This internal construction continues `HeightFiltration`. Its inputs are
actual finite subgroups, natural heights, and the sum bound for
commutators. `exactFactor H w d i` retains `H i` precisely when its height
equals `d`. `Layer H w hc d` is the actual group quotient of `level d` by
the subgroup of `level (d+1)` inside it; its group structure uses the
normality proved in `HeightFiltration`.

At a positive height `d`, the exact-height factors commute in the
quotient: their commutators belong to level `2d`, which lies in level
`d+1`. Their ordered product therefore defines the group homomorphism
`layerMap`.

When all heights are positive, `layerMap_surjective` starts with the
ordered coordinates for an element of level `d`. Coordinates below `d`
are already trivial; coordinates above `d` vanish in the quotient.
Keeping the exact-height coordinates gives the same quotient class.

If the full ordered-product map is also injective, a tuple in the kernel
of `layerMap` has its ordered product in the next level. This product
has another ordered factorization with every coordinate below `d+1`
trivial. Uniqueness equates the two factorizations and forces all
exact-height coordinates to be trivial. `layerMap_injective` implements
this argument, and `layerEquiv` is the resulting group isomorphism from
the product of the exact-height subgroups to the successive quotient.

The ordering need not agree with the heights. No commutativity
hypothesis on the input subgroups is needed: where uniqueness holds,
the constructed isomorphism and the quotient commutation force the
appropriate commutativity as a consequence.

The construction is derived group theory supporting the root-height
argument in Conrad, *Reductive group schemes* (2014), Theorem 5.4.3,
pp.174–177. It does not assert representability, smoothness, closedness,
an algebraic vector-group identification, or descent of vector bundles.
