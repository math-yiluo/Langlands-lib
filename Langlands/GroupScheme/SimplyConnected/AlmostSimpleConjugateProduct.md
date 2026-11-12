# The actual embedding-conjugate product

This internal construction by Worker 166 assembles the actual conjugate-factor
isomorphisms into an isomorphism from their categorical finite product to the
original upper-field group. It assumes an actual smooth affine almost-simple
product presentation after a Galois field extension, an affine almost-simple
original group with quasi-compact, quasi-separated, locally finitely presented
structure map, and a selected index.

`embeddingConjugateFamily` consists of scalar extensions of the actual selected
stabilizer-field model along every embedding of that field into the upper
field. `embeddingConjugateProductIso` applies the actual conjugate-factor
isomorphism in each coordinate, reindexes by the proved embedding-index
equivalence, and composes with the supplied original product presentation.

The projection identities retain the original coordinates: composing the
product comparison with an indexed factor projection equals projection onto
that embedding coordinate followed by its actual conjugate-factor comparison.
Equivalently, the inverse product isomorphism's embedding coordinate is the
original indexed factor projection followed by the inverse conjugate-factor
isomorphism.

This constructs the product of the actual conjugate groups and its original
coordinates, without assuming commutativity. Identification of that product
with base change of the existing affine Weil restriction, descent of the
resulting comparison, and absolute almost-simplicity over a separably closed
field remain further obligations.
