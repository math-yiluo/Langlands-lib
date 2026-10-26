# Strong irreducible constituents from unique atoms and coatoms

Author: Worker 502.

The theorem is
`Langlands.Classification.strongConstituentExtrema`, of exactly
`Langlands.Classification.StrongConstituentExtremaStatement`, at independent
group and carrier universes `uG` and `uV`.

For the head direction, take the unique coatom `S` and form the actual quotient
by its underlying submodule. The canonical quotient map is surjective with
kernel `S`. The published coatom-kernel criterion makes its target irreducible.
Every competing irreducible quotient map also has a coatom kernel, so uniqueness
of the coatom gives equality of kernels. This gives a strong head, and the
published canonical-head equivalence makes the canonical head a strong one.
Conversely, any coatom yields an actual irreducible quotient in the source
carrier universe. Strong head uniqueness identifies that quotient's kernel
with the kernel of the supplied strong head map, giving a unique coatom.

For the socle direction, first prove that the actual image of an injective
intertwiner from an irreducible representation is an atom. Restrict the
corresponding group-algebra linear map to its actual range; it is bijective.
Transport simplicity across it, and use the order isomorphism between
subrepresentations and group-algebra submodules. Now the inclusion of the unique
atom has irreducible source by the published atom criterion. All competing
irreducible embeddings have atom images, so their images coincide with that
atom. This yields a strong socle, which the canonical-socle theorem transports
to the canonical restriction. Conversely, inclusions of all atoms have
irreducible sources; strong socle image uniqueness makes every atom equal to
the supplied strong socle map's image.

All uniqueness is equality of actual subrepresentations and hence of the
underlying submodules in `ConstituentRelations`. The quotient and restriction
carriers stay in `Type uV`. The proof adds no finite length, topology,
smoothness, nonzero, or finite dimension hypothesis.

The route uses `Cosocle`, `CanonicalConstituents`, the generic atom lemma in
`Category.FiniteIndexRestriction`, and Mathlib's group-algebra simplicity
correspondences. No segment classification, analytic classification,
multisegment exhaustion, tempered uniqueness, or contragredient theorem is
used. This algebraic adapter alone does not prove that the segment inductions
have the required extrema or that their two canonical constituents agree.
