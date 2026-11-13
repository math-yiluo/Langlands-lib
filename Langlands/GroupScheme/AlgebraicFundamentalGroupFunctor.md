# Induced maps on algebraic fundamental groups

This module implements the map of KP Lemma 11.3.6 using the actual maximal-torus
presentations from `AlgebraicFundamentalGroup`. The source is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 11.3.6 and its proof, printed
pp. 427–428 / PDF pp. 458–459, source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The 1 November 2024 corrections do not change this item.

For a morphism `f : H → G`, source presentation `a`, and target maximal-torus
choice `b`, `Choice.IsTorusFactorization` says that a geometric torus morphism
`e : a.torus_E → b.torus_E` is the restriction of the actual scheme morphism
`f_E`. The equation uses the actual inclusions in `H_E` and `G_E`.

For a fixed target presentation `c`, `Choice.IsInducedMap` characterizes the
integral linear map by

`m([ν]_a) = comparison(b,c)([ν followed by e]_b)`.

It requires a torus factorization to exist, and requires this equation for
every such factorization. Thus a missing factorization cannot make the
characterization vacuous. The comparisons are those characterized by geometric
conjugation in Construction 11.3.1, rather than arbitrary lattice identifications.
`Choice.mapTo` selects a map by this predicate; `fundamentalGroupMap` uses the
fixed source and target choices. The definition neither assumes an induced
linear map nor takes a desired kernel as input.

The helper `mapTo_spec` proves only the implication from existence to the
selection law. Existence, uniqueness, factorization independence, Galois
equivariance, compatibility with all presentation changes, and the functor
laws remain unconditional Prop-valued obligations in the companion statement
module. KP constructs the map by a containing maximal torus and the induced
map on simply connected covers. This implementation states its effect on the
quotient representatives directly, retaining the obligation that the effect
exists and is unique. No perfectness, characteristic or splitness restriction
is imposed on the field or groups.
