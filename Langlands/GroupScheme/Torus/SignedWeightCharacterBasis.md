# Actual character bases from independent row decompositions

This internal prerequisite completes the algebraic passage from full-torus row
weight data to an actual-character formula on an isomorphic split torus. The
geometric hypotheses remain explicit.

`characterBasisOfNonoppositeBound` transports the coordinate basis chosen by
`SignedWeightAssembly.basisOfNonoppositeBound` through the actual-character
linear equivalence of `SignedWeightTransport`. The input is an actual group
scheme isomorphism from `S` to the coordinate split torus. The coordinate support
generates the integer lattice; its multiplicities are positive, symmetric under
negation, and have sum at most `r` on every nonopposite subfamily. The number of
coordinates is `r`.

`exists_characters_of_decomposition` accepts a finite-dimensional space `V` over
an arbitrary division ring `D`, with an independent family `W` of `D`-submodules
indexed by coordinate weights. A finite support `A` is exactly the set where
`W` is nonzero, and its subspaces span `V`. Its weights additively generate the
integer coordinate lattice, opposite occurring weight spaces have equal
`D`-dimensions, and the dimension sum on each nonopposite subfamily is at most
`r`. The coordinate rank is `r`.

The theorem first derives positive dimensions on the support from nonvanishing
of finite-dimensional subspaces. Equal opposite dimensions then make the
support symmetric. `SignedWeightAssembly` gives an integral `Fin r` basis with
exact signed nonzero support and multiplicity one. The transported basis is
therefore an actual family of characters, linearly independent over the
integers. `SignedWeightTransport.characterBasis_detects_cocharacters` proves
that the family detects every cocharacter.

A family `F ν c` of subspaces is supplied with the explicit equality that it
groups the spaces `W m` by the pairing of their transported characters with `ν`.
Applying the signed count proves its dimension equals the number of signed
basis indices with pairing `c`, plus `finrank D V - 2 * r` when `c = 0`. If zero
is absent from `A`, exactness of the support gives `W 0 = ⊥`, so the same argument
handles that case. The proof uses the residual dimension identity, rather than
assuming the nonnegative subtraction formula independently.

The provenance is internal: the construction combines the signed-support
assembly and actual-character transport with elementary nonvanishing criteria
for finite-dimensional subspaces. It assumes the row decomposition, generation,
opposite dimension equality, the nonopposite bound, coordinate rank equality
and the grouping comparison. It proves no new geometric hypothesis and is not
an unconditional proof of the isometry maximal-split-torus statement. The base
field and division ring have arbitrary characteristic and cardinality.
