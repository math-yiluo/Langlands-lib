# Algebraic independence from primitive Laurent Frobenius coordinates

This internal support result connects the finite Laurent Frobenius encoding
to the primitive polynomial-relation theorem. The coefficient field has prime
characteristic; the bialgebra and character index have independent universes.

Additive one-variable substitution preserves the Laurent augmentation kernel.
Finite encoding commutes with such substitutions: only prime-power monomials
can have nonzero coefficients, and the encoding is linear and compatible with
iterated Frobenius powers.

For a finite primitive family in a commutative bialgebra and an algebra map
from that bialgebra to Laurent functions, suppose the coordinate pullbacks
vanish at the identity, their finite encodings are injectively indexed, and
the finite set of those encodings is Frobenius-independent. The family is
algebraically independent. A nonzero polynomial relation yields a nonzero
additive relation by PrimitivePolynomialRelations. Its one-variable parts
give a relation between the encodings, so every part vanishes by Frobenius
independence. Universal additivity expresses the relation as their sum, a
contradiction.

No finite generation of all primitive functions is assumed. This result does
not supply primitive algebra generators or a split series.

`FrobIndep.indexed` is the auxiliary conversion from a finite-set predicate
to an injectively indexed family. It extends the given family of additive
one-variable polynomials to the ambient polynomial type, applies finite-set
independence, and reads the result at each index. Empty families are allowed.

In `algebraicIndependent_of_frobIndep_encoding`, the Laurent algebra map
itself need not be injective. Its values on the chosen generators must be
the specified pointed functions; injectivity is required of their indexed
finite encodings. No orbit-support containment premise is needed. Finite
encoding is used only as a linear map compatible with Frobenius and additive
substitution. The primitive polynomial relation theorem supplies the passage
from additive independence to algebraic independence, so multiplicativity of
the encoding is neither required nor claimed.

The implemented proof of substitution compatibility expands a one-variable
polynomial over its coefficient support. Its zero constant coefficient gives
pointedness of every term. The classification of additive polynomial support
over a characteristic-p field leaves only degrees p^r, where the existing
`finiteEncoding_frobPower` applies. This is internal derived content using
`TorusLinearization.AdditivePolynomials`, `TorusLinearization.Euclid`,
`LaurentFiniteFrobeniusBasis` and `PrimitivePolynomialRelations`. It retains
finite and imperfect fields and imposes no smoothness assumption on the
bialgebra.
