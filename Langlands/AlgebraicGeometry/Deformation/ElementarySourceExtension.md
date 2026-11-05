# Canonical elementary extension of an actual local presentation

This internal algebra construction starts with a Noetherian local
`k`-algebra `R`, a specified surjective augmentation `ε : R → K`, an
actual augmented Artinian test `A`, and a compatible algebra map
`π : R → A`. Write `m` for the actual maximal ideal of `R` and `J` for
the actual kernel of `π`. No coefficient-field section is used.

The defining ideal is `m J`. It lies in `J` and hence in the kernel of
the specified augmentation. The augmentation therefore descends to
`Q = R/(m J)` and remains surjective. Since the compatible map to `A`
kills a positive power of `m`, so does `m J`. The quotient is
Noetherian and local with nilpotent maximal ideal, hence Artinian.
`test` bundles this actual quotient and its actual augmentation.

The map `π` descends to `reduction : Q → A`, and
`reduction_projection` proves the exact original algebra-map equation.
If `π` is surjective, so is `reduction`. Its actual kernel is the image
of `J` in `Q`, and mapping the product `m J` into `Q` gives zero.
Thus the maximal ideal of `Q` annihilates that kernel: `reduction` is
an elementary surjection in the existing augmented Artinian category.
Its kernel can have any finite dimension, including zero.

The existing `ArtinianTest.ElementaryKernel` construction therefore
equips the unchanged actual kernel with its unique residue-field
module recovering the original source action. `kernel_finiteDimensional`
records its finite dimensionality.

For any elementary arrow `q : B → A` and any algebra map `β : R → B`
whose composite with `q` is `π`, the augmentation equation follows
automatically. The image of `m` lies in the maximal ideal of `B`, and
the image of `J` lies in `ker q`. The elementary condition kills their
product, so `β` kills `m J`. `factor` is the induced actual test arrow
`Q → B`. Its composite from `R` is exactly `β`, and its composite
with `q` is exactly `reduction`. Quotient-map surjectivity gives
uniqueness. `existsUnique_factor` states both equations and uniqueness.
Neither surjectivity of `β` nor a coefficient-field section is needed.

When `k` is Noetherian and `K` is finite as a `k`-module, the published
construction `ArtinianPolynomialPresentation` supplies a surjective
compatible map from an actual completed local polynomial source onto
the whole test `A`. The aliases `polynomialTest`,
`polynomialProjection` and `polynomialReduction` specialize the generic
construction to precisely that source and that cover.
`polynomialReduction_elementary` and
`polynomialReduction_projection` retain its elementary property and
exact cover equation. All constructions preserve the arbitrary common
universe `u`.

The provenance is internal quotient algebra, the published bound on
maps from a local algebra to an actual Artinian test, and the
Noetherian local nilpotence criterion for an Artinian ring. The
universal factorization uses only the defining maximal-ideal
annihilation condition and the ordinary quotient universal property.
The generic source need not be complete. This construction supplies
an actual finite elementary extension on which an obstruction can be
evaluated; it does not assert vanishing of that obstruction or yet
construct a Picard family, hull, formal versality or atlas.
