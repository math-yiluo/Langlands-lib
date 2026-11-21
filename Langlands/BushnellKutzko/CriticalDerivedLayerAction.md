# Residual field action on lattice layers

This is an internal step in the cyclic lift for Bushnell–Kutzko (1993),
(2.4.1)(iii). It develops the successive-quotient argument of §2.5, rather
than stating a separate result from the book.

Order elements act on each layer, and shifting units carry a layer
isomorphically to the translated layer. Their original integer-linearity
implies residue-linearity by surjectivity of the residue map. If an integral
polynomial evaluates to filtration depth at least one, its reduction
annihilates the layer action of the endomorphism. Evaluation thus descends
from the residue polynomial ring to its quotient. The Lean construction uses
an algebra homomorphism into the possibly noncommutative endomorphism ring;
the underlying action supplies the scalar tower on the layer.

For an irreducible monic residual polynomial, a linear combination of the
short root powers with a nonzero residual coefficient is a nonzero field
scalar by the power basis. Its action on each layer is injective. Any order
element with injective layer actions preserves exact vector depths, hence is
injective and, by finite dimensionality, invertible. Its inverse also
preserves the lattices, so the original element is a shifting unit of degree
zero.
