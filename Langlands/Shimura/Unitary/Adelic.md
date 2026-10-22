# Actual topological and finite adelic similitude points

Author: Worker 57. This construction is a prerequisite of the arithmetic
specialization of the Harris level tower.

`AlgebraInvolution.Points` is the previously constructed similitude subgroup
over the actual scalar extension `S ⊗[R] A`, with a named carrier. Its topology
comes from Mathlib's module topology over `S`, the units topology recording
both value and inverse, and the subgroup topology. A finite `R`-module
algebra `A` gives a finite `S`-module scalar extension; Mathlib's
`IsModuleTopology.isTopologicalRing` then proves the topological group
certificate. No topology on the original algebra is required.
`coordinateEquiv` identifies this tensor-module topology with the ordinary
finite product topology through every supplied finite basis. Thus no basis
choice is hidden in the topology.

`pointsMap` uses the actual tensor coefficient map and proves multiplier
compatibility. A continuous coefficient algebra map induces a continuous
point-group map, using the module topology universal property followed by
the units and subgroup topologies. `diagonalPoints` sends the original group
to the scalar extension by the tensor inclusion; its multiplier is the
corresponding scalar unit.

The rational specialization uses the published `Langlands.Global.FiniteAdeles`
and `FiniteCompletion` interfaces, hence actual restricted products and
completions. In particular the multiplier is a rational finite adele, rather
than independent multipliers over the totally real center. The local
evaluation maps are continuous. Evaluation of a diagonal rational point
equals its direct local scalar extension.

The general base, algebra and coefficient carriers retain independent
universes. Finiteness is required precisely for the topological ring/group
and continuity results using multiplication; it is not silently assumed
in the purely algebraic point groups. In the Harris specialization this
finiteness follows from the given central-simple finite-dimensional algebra
over a number field.

This is a derived implementation of the finite-adelic group and rational
diagonal appearing in Harris (1997), Section 2, printed pages 88-90, and
Harris (1999), Section 4, printed pages 308-309, with the rational multiplier
convention of Kottwitz (1992), printed page 654. These original passages
were read. The finite-module topology argument is provided by the pinned
Mathlib declarations, not asserted as a theorem from those articles.
No affine representability, adelic decomposition of a prescribed inner
form, compact-open subgroup existence, Shimura scheme, or local system
is asserted by this module.

Source fingerprints: Harris (1997), `harris-1997-drinfeld-cohomology`,
SHA-256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`;
Harris (1999), `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
Kottwitz (1992), `kottwitz-1992-lambda-adic-simple-shimura`,
SHA-256 `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
Formal dependencies are the published `Unitary.Similitude`, `Global.Adelic`,
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.
