# Full-dual coefficients from an open subgroup

This internal unit assembles the published same-level
`smoothDualFixedExtension` with the published smooth-dual comparison for
restriction to an open subgroup. It adds no new functional-extension
principle. The ambient group, source carrier and ambient carrier occupy
independent universes.

Let `H` be an actual open subgroup of a topological group `G`, let `ρ` be a
smooth complex representation of `H`, and let `σ` be a smooth complex
representation of `G`. Supply an injective intertwiner from `ρ` into the
actual restriction of `σ`. For every compact open subgroup `K` of `H` and
every algebraic functional `ℓ` invariant under `K`,
`exists_open_subgroup_coefficient_extension` supplies an actual member of the
full ambient smooth dual. It retains invariance under the image of `K` in
`G`. The intertwiner takes every `K`-fixed vector to a vector fixed under this
same image subgroup. For every source vector and every element `h` of `H`,
the ambient inverse coefficient at the actual image of `h` equals the
original inverse coefficient.

The proof views `ℓ` as a `K`-fixed smooth functional. The published
`smoothDualFixedExtension` extends it to the smooth dual of the restricted
ambient action at exactly `K`; its published inverse-coefficient law gives
the required equality on every vector. Openness of `H` identifies smoothness
of this functional for the restricted and ambient dual actions. Invariance
under the image subgroup follows from its `K`-fixed property. Intertwining
gives the fixed-vector assertion.

`openSubgroupDualExtension` chooses such an ambient smooth functional, and
`openSubgroupDualExtension_spec` records these three properties.
`support_openSubgroupDualExtension_inverseCoefficient` identifies the whole
source inverse-coefficient support with the preimage of the ambient support
under the actual subgroup inclusion. This is equality of ordinary function
supports, with the inverse convention of the uniform-support target.

No level is shrunk. No admissibility, finite dimension, irreducibility,
compact coefficient condition, ambient cuspidality, or ambient embedding
existence is assumed or concluded. A common compact bound across ambient
representations remains a separate obligation in the norm-kernel
uniform-support proof.
