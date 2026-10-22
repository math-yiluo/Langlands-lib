# P-adic opposite Levi decomposition

Author: Worker 6. This module pairs with `Langlands.Group.GL.OppositeBlocks`
and imports the independently published `Langlands.Group.GL.PadicBlocks`.

For every prime `p`, every algebraic `PadicField p`, every supplied
`F.TopologicalData`, and every ordered positive `BlockShape n`, this module
specializes the actual constructions in `OppositeBlocks`. It uses the same opposite
parabolic and product Levi topologies already exported by `PadicBlocks`.

`oppositeUnipotentRadicalTopology` is the inherited subgroup topology for the
kernel of the actual opposite Levi projection. Topological group and Hausdorff
certificates follow from the ambient actual general linear group. Local compactness
uses the proved closedness of the opposite parabolic and its kernel; the field's
Hausdorff premise follows from the compatible right uniform structure of the
supplied local field. No local compactness or separation assertion is supplied as
an extra premise on the radical.

`oppositeBlockLeviProjection` and `oppositeBlockLeviSection` package the actual
diagonal extraction and common block diagonal inclusion as continuous homomorphisms.
`oppositeBlockDecomposition` specializes the proved homeomorphism
`P⁻ ≃ U⁻ × M`, with inverse `(u,m) ↦ u * section(m)`. The action continuity
certificate specializes continuous conjugation by that same common Levi section.
All multiplication, inverse, subgroup, and factorization proofs are inherited from
`OppositeBlocks`, whose paired Markdown gives their implementation.

The canonical abbreviations apply these constructions to the accepted
`F.canonicalTopologicalData`. They cover topology, group continuity, separation,
local compactness, projection, section, decomposition and action continuity for
every supplied algebraic p-adic field. Local instance installation preserves the
exact chosen realization and introduces no competing global topology.

This is an internal specialization of `OppositeBlocks` and `PadicBlocks`, not a
theorem about Jacquet duality, compact exhaustion, quotient compactness, or modulus
normalization. Its original block-geometry provenance is documented in `Blocks.md`.
