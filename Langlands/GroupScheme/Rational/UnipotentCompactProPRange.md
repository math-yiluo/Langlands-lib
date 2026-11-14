# Compact pro-p subgroups in closed unipotent images

This internal construction transfers the compact-unipotent pro-p result to
the actual ambient rational-point subgroup.

For a topologically embedded homomorphism and a subgroup contained in its
range, `subgroupComapHomeomorphOfEmbedding` identifies the subgroup with its
inverse image. The map is the original homomorphism restricted on both
sides. Injectivity comes from the embedding, surjectivity from range
containment, and the two original subspace topologies give a homeomorphism.
The source and target have independent universes; no topological-group
instance is required.

For a closed embedding, a compact subgroup has compact inverse image.
The preceding homeomorphism therefore transfers the pro-p property from
that inverse image. This proves `isProPSubgroup_of_isCompact_le_range`
from the premise that all compact source subgroups are pro-p.

A closed immersion of an affine unipotent group of finite type into an
affine group gives a closed embedding on the actual local rational points.
Its source is affine by closedness. The compact-unipotent theorem applies
to every compact inverse-image subgroup, proving that every compact ambient
subgroup contained in this rational-point image is pro-p for the actual
residue characteristic. No smoothness, splitness, or ambient finite-type
assumption is added.

The provenance is composition of the canonical closed-immersion point
topology, compact inverse images, the proved compact-unipotent result and
pro-p transport through a continuous multiplicative equivalence. This is
a prerequisite for the maximal pro-p argument and makes no maximality
claim.
