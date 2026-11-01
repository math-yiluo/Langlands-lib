# Schematic closure of a generic section

This proof supports the integral-base specialization of EGA IV,
fourth part, Proposition 18.10.19, printed p.167. Its source is the registered
original `grothendieck-dieudonne-ega-iv4-1967`.

The first two internal lemmas show that the schematic image of a quasi-compact
morphism from an integral scheme is integral. The map to the schematic image
is scheme-theoretically dominant, as follows from Mathlib's injectivity of
its maps on sections over the inverse images of affine opens. Reducedness
then descends from the source. Its support is the closure of an irreducible
image, and hence is irreducible.

The imported `UnramifiedSections` lemma shows that a morphism whose composite with a locally
finite type, formally unramified morphism is an open immersion is itself an
open immersion. It factors the morphism through a pullback of the diagonal
and an open base change of the composite. Both factors are open immersions.

The next lemma spreads an actual generic section of an integral target into
a partial section on a dense open of the integral base using Mathlib's
`Scheme.PartialMap.ofFromSpecStalk`. Its composite with the target's map to
the base is the dense open inclusion. The imported lemma makes the partial
section an open immersion. Its image is a nonempty open in an integral
scheme, hence dense. These two dominant open immersions exhibit birationality
over the base.

The next lemma applies this argument to the schematic image of a generic
field map. Its one-point source makes the map quasi-compact without any
quasi-compactness assumption on an open of the base. The first two lemmas
then make the image integral, and the induced generic lift satisfies the
same equation over the base. Formal unramifiedness and local finite type
pass to its map to the base by composition with the image inclusion.

`genericSectionSchematicClosure` proves exactly the proposition
`GenericSectionSchematicClosureStatement` using this last lemma.
These are supporting results; they do not yet prove generic-section extension.
