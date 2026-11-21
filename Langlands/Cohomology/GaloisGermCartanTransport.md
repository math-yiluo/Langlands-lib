# Galois–Čech covers computed on cofinal germ systems

An initial reindexing of a section diagram induces a natural isomorphism
of its germs. The comparison sends the germ of a section at a retained
stage to the germ of the same section after reindexing.

`GermCover` presents a cover between two functors to modules by cofiltered
diagrams with a `GermGaloisDatum` and isomorphisms to the two germ functors.
The diagrams may depend on the cover. The proof transports the deck action
by conjugation and transports restriction by composing with the two
isomorphisms. The isomorphism on the cover functor is equivariant.
Injectivity, invariants descent, and injective acyclicity follow from
the corresponding theorems on the supplied diagram.

Given a family of these covers with the local lifting property for short
exact sequences, `galoisCechSystemOfGermCovers` assembles the data for
the Galois–Cartan criterion. This internal construction allows a pointed
analytic cover to be defined over a smaller neighbourhood than the ones
used to present either of the original germ functors.
