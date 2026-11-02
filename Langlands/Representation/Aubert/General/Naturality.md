# Naturality of the actual normalized complex

Internal construction by Worker 194, using Worker 23's normalization
adapter and the published generic signed-diagram and subgroup naturality results.

`termMap` is the actual normalized induction–Jacquet functor applied to an
ambient smooth morphism. The adapter's natural normalization comparison proves
`termEquiv_map`. Transporting through that comparison and the canonical subgroup
quotient naturality square gives `termMap_natural` for the actual transitions.
The degree map is the finite coordinate product, with equivariance checked on
each coordinate. The generic signed-diagram map lemma proves its chain-map law
without changing the exterior signs. Identity and composition descend from the
actual term functor laws, and `degreeFunctor` bundles the homogeneous construction.

`boundary_map_le` follows from the chain-map law. The actual quotient universal
property defines `terminalMap`; equivariance is checked on representatives.
`terminalMap_comp_projection` records the natural projection square. Identity and
composition are proved after precomposing with the surjective quotient projection,
using the corresponding degree-map laws. `terminalFunctor` bundles these maps;
`sharpFunctor I` chooses degree `|ι| - |I|`. The signed differentials and the
quotient projections are actual natural transformations `differentialNat` and
`terminalProjectionNat`. No exactness,
support, finite length or irreducibility assertion is made.
