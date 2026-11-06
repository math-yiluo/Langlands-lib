# Saturation of product covers from finite intersection comparisons

Worker 1685 derives the saturation condition needed by the finite intersection
recognition interface from actual product-domain inverse images. This is
internal infrastructure composed from finite full-domain covers, literal
relative domains, actual product domains and the local-domain category.
Worker 1582 authored the reused generalized product-domain construction.

`ambient_eq_of_finiteCover` starts with a finite full-domain cover of a candidate
affinoid algebra `Q`, local domains `Pᵢ` including into both `U` and `V`, and
bounded equivalences from the cover algebras to the `Pᵢ` algebras. The two
equations compare entire bounded algebra maps over the proposed maps `f` and
`g`. Every point of the spectrum of `Q` lifts to one cover component.
Transporting that lift through its bounded algebra equivalence and applying
inclusion naturality identifies both ambient images with the same point of
`Pᵢ`. The two ambient maps therefore agree on all of `Q`. This argument uses
neither saturation nor a global represented-domain property for `f` or `g`.

For any bounded map `q` from the actual coproduct of the unchanged `U` and `V`
algebras into `Q`, the two global maps are its composites with the coproduct
legs. If their ambient maps agree, `pullback_product_locus_of_ambient_eq` proves
that pulling back the actual product of the relative domains of `S → U` and
`T → V` gives exactly the inverse image of the literal intersection of the
ambient loci of `S` and `T`. The proof expands the actual product and pullback
loci, then uses ambient equality for the second membership condition.

`FiniteIntersectionData.ofProductCover` combines these two results. Its inputs
are the actual finite cover, local bounded comparisons and exact map equations;
each cover locus must be the pullback of the specified product of relative
domains, and each local piece must have the corresponding intersection locus.
The union of the local pieces must be the intersection of `U` and `V`. These
inputs derive saturation and construct the complete finite-recognition data.
In particular, saturation is not an additional input to this constructor.
The previously constructed recognition interface then proves global spectral
injectivity and the full domain property while preserving `Q` and the proposed
maps.

The module does not construct the global quotient or its local algebra
equivalences, prove ideal-descent effectiveness, or prove admissibility of the
global tensor map. Those remain obligations of the special-set intersection
proof. No closed-quotient property of `q` is needed for the saturation argument.
Coefficient, ambient and original-index universes remain independent; trivial
valuations, arbitrary positive radii, nonreduced and zero algebras, empty
spectra and finite covers of size zero are permitted. The ambient space is
only assumed to be a topological space.
