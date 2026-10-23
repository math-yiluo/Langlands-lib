# Torus expansions for coefficient models

`CoefficientTorusExpansion` expresses the full diagonal-torus expansion for
all actual coefficient-model vectors of a representation and a specified
upper-unipotent character. A single finite set of continuous functions with
finite-dimensional translation span is chosen before the functional and model
vector. The Schwartz–Bruhat coefficients may depend on both. The coordinates
are the consecutive diagonal ratios; the final central coordinate remains
unrestricted in the finite functions. Rank one is included, with a
zero-dimensional Schwartz–Bruhat coefficient space.

`ModelAsymptoticTransferStatement` is an internal conditional transport target.
It assumes the Library proposition `WhittakerTypeAsymptoticStatement` and
concludes `CoefficientTorusExpansion` for every supplied `F.TopologicalData`,
every positive rank, and every representation satisfying `IsOfWhittakerType`.
The specified unipotent character can be either the standard character or its
inverse. Irreducibility is not required. The field and representation universes
remain independent. The target does not assert the analytic expansion without
the stated prerequisite.

The mathematical source of the assumed expansion is JPS (1979), Proposition
2.2 and Remark 2.2.5, printed pages 181–183, as recalled by JPSS (1983), section
2.5, printed pages 388–389, and used in its proof of Theorem 2.7 on pages
391–392. The precise full-torus extension is documented in
`Whittaker/AsymptoticStatement.md`. This file introduces no new version of that
source theorem. It states the adapter required because the published analytic
integrals use coefficient-image vectors and a supplied field topology, whereas
the expansion target uses linear functionals and the canonical topology.

The intended transport uses equality of the supplied and canonical topologies,
the one-dimensional functional space already included in `IsOfWhittakerType`,
and surjectivity onto the coefficient image. Replacing the additive character
by its pullback under multiplication by `-1` covers the inverse sign. These are
the reasons this is a derived interface; none of these transport steps is
asserted proved in this statement file.

Sources: `jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`;
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
