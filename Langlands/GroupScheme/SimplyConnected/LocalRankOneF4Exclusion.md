# Conditional exclusion of a local rank-one F₄ index

`localRankOneTypeF4_false_of_components` excludes an actual type-F₄ Tits index
of split rank one over a nonarchimedean local field, under the explicit
`LocalAnisotropicCartanComponentsStatement` premise. This is an internal
derived consequence. The component premise remains unproved here.

The oriented actual F₄ Cartan matrix is rigid, so the full absolute Galois
star action is trivial. The published rank-one orbit comparison then gives
exactly one distinguished simple vertex.

If that vertex is either endpoint, the two middle vertices have zero
restriction. Their actual Cartan entries are −2 and −1 in opposite directions.
This contradicts symmetry of the actual zero diagram, transported from the
type-A anisotropic components by `zero_cartan_symmetric_of_local_components`.

For either middle marking, the explicit seven-reflection construction
`CartanF4Root.isRoot_highest` supplies an actual root with coefficients
`(2, 3, 4, 2)`. The additive restriction map kills every simple root except the
distinguished one. Hence the constructed root restricts to three or four times
that distinguished restriction. The published relative-root multiple bound,
which allows nonreduced root systems, excludes both possibilities.

The proof preserves arbitrary field and residue characteristics, including
characteristic two, and every universe parameter. It uses actual Cartan entries,
actual roots and the full star action. It assumes neither a downstream local
classification nor local Kneser–Tits, and proves no unconditional enumeration.
