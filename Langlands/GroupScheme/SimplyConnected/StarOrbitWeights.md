# Integral fundamental weights over full star orbits

Author: Worker 177.

This is an internal construction from the actual integral fundamental-weight
basis and the full absolute star action of a simply connected group. It works
over every field and in every characteristic. Its input is actual
`TitsIndexData d` for an affine, locally finite type semisimple group.

`absoluteFundamentalCharacter_star` specializes the imported covariance of
the integral fundamental-weight basis under based root-datum automorphisms.
The fundamental weight at a vertex is transported to the fundamental weight
at its star translate.

`absoluteOrbitWeight hsc a` sums those actual integral fundamental weights
over the finite full-star orbit of `a`, counting each vertex once. Its
star-invariance theorem applies the preceding covariance and reindexes the
sum using the star permutation of that finite orbit. This is invariance
under the star action on the weight lattice.

The pointwise fixer of the actual vertex field fixes its fundamental weight
under the star action in the original separable closure. The proof combines
the published fixed-field/stabilizer equality with fundamental-weight
covariance. It constructs no new pinning after extending the ground field.

Restriction of an orbit weight to the constructed full geometric centre
equals the corresponding `centerOrbitCharacter`, by additivity of actual
character restriction. For a globally fixed vertex, the singleton-orbit
formula identifies the orbit weight with its fundamental weight.

For a complete D4 Cartan numbering, vertex 1 is central and vertices 0, 2
and 3 are the leaves. If no leaf is globally fixed, the imported exact
leaf-orbit theorem identifies every leaf orbit with these three vertices.
Consequently its orbit weight is `d4LeafWeightSum`, the actual sum of the
three integral fundamental leaf weights. The imported integral D4 identity
expresses that sum as
`2 alpha_0 + 3 alpha_1 + 2 alpha_2 + 2 alpha_3`, proving membership in the
actual integral root lattice.

The provenance is the stated internal chain of finite-orbit, integral-basis
and root-lattice deductions. No Tits algebra, Brauer obstruction,
corestriction, field-extension comparison, anisotropic-kernel comparison or
local-index exclusion is constructed or assumed. These weight identities
provide inputs for such comparisons; they do not prove the local
rank-one enumeration.
