# Corrected fundamental positive generators in the actual rational norm kernel

This is an internal construction toward the class-uniform coefficient-support
argument. It uses actual simple relative roots, actual cocharacters and the actual
common rational norm kernel. It does not prove a simultaneous compact-open level,
a Cartan covering, or the final uniform-support proposition.

For each actual simple root `α`, `fundamentalRootFace` omits exactly `α`.
`NormKernelFundamentalCocharacters` consists of standard cocharacters for those
faces which annihilate all restricted ambient rational characters. Its existence
is derived from the host standard-cocharacter statement by the published integral
Weyl correction. The correction preserves standardness and kills all restricted
ambient characters. This also covers an empty simple-root type.

The diagonal simple-root pairings are positive and the off-diagonal pairings
vanish. `orthantCocharacter` sums the nonnegative integral multiples of these
directions, so its simple-root coordinates are the corresponding exponents times
positive diagonal weights. This proves that the lattice map is injective and
that every ambient character annihilates its image.

`orthantHom` evaluates the entire lattice map at the same canonical order-one
field uniformizer, then maps into the actual group and restricts its codomain to
the actual common norm kernel. All its points lie in the torus image and therefore
in every standard Levi; they commute. For a maximal split torus embedding this
map is injective: cancel the monomorphic torus map, apply the intrinsic
character-valuation formula, and recover each exponent from its positive
diagonal weight. Its coordinate rays are the powers of
`generator`, whose values are precisely the specified cocharacters evaluated at
that uniformizer.

The canonical uniformizer's powers tend to zero because order one means its
canonical valuation is less than one; the valued-field power convergence theorem
then applies.

All topology in the final section is the canonical rational-point topology,
with the common norm kernel carrying the inherited subgroup topology.
`generator_escapes` uses the omitted root as a positive character. The torus
embedding is closed and both schemes are affine, so the imported
positive-character escape theorem applies to compact ambient sets. Continuous
inclusion into the ambient group then gives escape from compact sets in the
actual kernel. This argument needs no local compactness hypothesis on the
ambient group.

Under the host connected-reductive, maximal-split-torus, generic-cocharacter,
standard-cocharacter and ambient topological-group premises, and closedness of
the corresponding actual radical, `generator_oppositeIwahoriBasis` applies the
specified-value basis theorem to this same corrected cocharacter and same
canonical uniformizer. It supplies centralization of the corresponding Levi
and a cofinal opposite Iwahori contraction basis for the specified generator.
`escapingData` packages these results with its standardness and escape.
Its cocharacter and element fields are definitionally the chosen direction
and generator. The bases here are constructed separately for each coordinate;
no simultaneous common level is asserted.

The provenance is internal. These constructions combine the existing integral
Weyl correction, intrinsic common-uniformizer evaluation, specified-value
Iwahori bases and positive-character compact escape. They introduce no further
geometric existence premise and do not change the uniform-support target or
its imported pairs.
