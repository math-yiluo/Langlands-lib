# Actual Weil factors in simply connected central covers

This is a derived internal construction using the published arbitrary-field
normal complement, simply connected finite product, almost-simple Weil
restriction, and split-rank comparison theorems. It supplies the actual group
part of the Cartan component realization problem, without asserting a
comparison of root diagrams or star actions.

`SimplyConnectedWeilFactor j` retains a prescribed almost-simple insertion
`j : A → C`. It records a finite separable extension `E/k`, an actual affine
simply connected absolutely almost-simple group `H/E` of locally finite type,
a Weil presentation `A ≅ Res(H)`, a simply connected group `N/k`, and an actual
isomorphism `Res(H) × N ≅ C`. The isomorphism identifies the left insertion
with the original `j` through the Weil presentation. Its source is explicitly
simply connected.

For a central isogeny `π : C → G`, `cover` is the composite of the product
isomorphism with `π`. The central-isogeny lemma retains the full
scheme-theoretic kernel condition; `left_cover` retains the original factor
map. For any finite `π` into an affine anisotropic `G`, a closed `j` implies
that `H` is anisotropic: finite maps do not decrease split rank, closed
subgroups do not increase it, isomorphisms preserve it, and the published
Weil-restriction comparison equates the ranks of `Res(H)` and `H`.

For a prescribed factor of `SimplyConnectedAlmostSimpleProduct C`,
`nonempty_weilFactor` and `weilFactor` produce these data. The original factor
is a smooth connected closed normal subgroup. The published normal-complement
theorem supplies `N` with central-isogeny multiplication `A × N → C`.
Simple connectedness of `C` makes that multiplication an isomorphism and
implies simple connectedness of `N`. The almost-simple Weil theorem gives
`A ≅ Res(H)`; replacing the left coordinate yields the product isomorphism.
The all-test multiplication formula proves the original insertion equality.
The construction has no characteristic restriction and works at every
universe parameter `u`.
