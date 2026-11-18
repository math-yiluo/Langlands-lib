# Full star-action comparison under extension of the ground field

Worker 509. This is derived interface material for actual Galois pinning data
over arbitrary fields and at every universe parameter. It uses the existing
root-datum existence and torus-compatible group-isomorphism comparison, the
character scalar-extension comparison, and uniqueness of the Weyl-corrected
based representative. It requires no finite-dimensional, separable, or Galois
hypothesis on the scalar tower.

`starAction_comp_of_character_intertwining` applies to Galois pinning data of
two groups over possibly different ground fields and splitting fields. A full
root-datum equivalence preserving their chosen bases and intertwining the
ordinary character actions intertwines the star actions of the two specified
automorphisms. To prove this, conjugate the ordinary root-datum action through
the equivalence. Equality of weight maps gives equality of root-datum
automorphisms. Their quotient is therefore the identity Weyl element, and
uniqueness of the based representative in that Weyl coset gives the star
comparison. The root-datum action, not only its restriction to vertices, is
compared.

For a tower `k → E → L`, `GaloisPinningData.ScalarExtension p` retains actual
Galois pinning data of `G_E` over `L`, a full equivalence of the original root
datum with the new root datum, preservation of the chosen bases, and
intertwining of the star action of every `E`-automorphism of `L` with that same
automorphism regarded over `k`. Full root-datum equivalence preserves every
ordered integral Cartan entry. The interface also retains the actual canonical
ambient tower isomorphism, the actual split torus comparison, their exact
inclusion square, and the literal character weight formula. These fields expose
the geometric comparison used in the construction, so actual subgroup factor
indices can be transported without assuming that a Cartan/star equivalence
alone determines the geometric labeling.

`nonempty_scalarExtension` constructs this data. The torus is the base change
of the original ground-field torus to `E`, with the base-changed inclusion.
The canonical tower isomorphisms identify its base change to `L` and the
ambient group with the original split pair over `L`. They transport connected
reductivity, splitness, and maximality. Root-datum existence supplies an actual
root datum of the new pair. The inverse tower isomorphisms induce a full
root-datum equivalence whose weight map is precisely precomposition by the
inverse torus tower map. Map the original base through this equivalence, and
construct simple-root pinning vectors by `RootPinning.ofSplitMaximalTorus`.
The character scalar-extension theorem supplies the ordinary-action
intertwining equality, and the first lemma gives the full-star equality for
every relative automorphism. `scalarExtension` chooses the resulting complete
comparison.

`RootDatumScalarExtension` records the pinning, root-datum equivalence, base
comparison and star-action equality. Its existence follows by projecting these
four fields from `ScalarExtension`. The separable-closure comparison uses
`rootDatumScalarExtension` to choose a witness of this four-field record.

The provenance is internal derived compatibility of published constructions.
This unit changes the ground field while keeping the common splitting field.
It does not identify a chosen Cartan component with an actual almost-simple
factor, and does not prove `SemisimpleTitsComponentFactorStatement`. It uses no
local rank-one classification or Kneser–Tits theorem.
