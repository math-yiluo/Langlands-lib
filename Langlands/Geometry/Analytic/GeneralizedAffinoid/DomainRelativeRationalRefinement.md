# Rational refinement over the actual containing domain algebra

Author: Worker 36.

Let `K` be a complete ultrametric normed field, `A` an actual presented
positive-polyradius affinoid algebra, and `U` a full represented domain
over `A`. This internal construction refines any finite full-domain cover
`c` of `U` by rational charts over the stored algebra `U.algebra`.

`FiniteCover.RelativeRationalRefinement c` records a finite family of
these rational charts, their pointwise coverage of the entire spectrum
of `U.algebra`, and a chosen component of `c` for each chart. Its
component arrow is an actual bounded restriction from the original
component algebra to the chart algebra, after extending the chart's
domain representation to `A`.

`relativeRationalRefinement c` constructs all this data. It regards each
original component as a full domain over `U.algebra` using
`Domain.relative`, chooses its published finite rational cover, and
flattens the finite dependent family. Injectivity of the full domain's
structural spectrum map, supplied by `DomainLocalization`, identifies
each relative locus with the full inverse image. Consequently the
chosen rational charts cover the whole spectrum of `U.algebra`.
The extended component arrows retain the chosen bounded restrictions;
their equations over `A` follow by composition with `U.baseMap`.

`map_comp` proves that the chosen arrow through the original cover
equals the direct extended inclusion. `restriction_comp` gives the
corresponding equation of actual bounded algebra maps.
`covers_ambient` transports coverage to the represented locus of `U`.
`toFiniteCover` and `toRefinement` package the extended family as a
finite cover of `U` and an actual refinement of `c`.

This is an internal derivation from the published full-domain
localization and unconditional finite rational coverage. It introduces
no new original-source assertion or private peer draft. All positive
radii and trivial valuations remain allowed, and the construction
requires no nonzero algebra or nonempty cover or spectrum.
It supplies refinement data for algebra descent; it asserts no new
algebra gluing or sheaf theorem.
