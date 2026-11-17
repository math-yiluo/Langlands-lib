# Local character descriptions of diagonal bialgebra automorphisms

This internal derivation strengthens the existing principal isomorphism certificate.
For a bialgebra equivalence between diagonal group algebras whose source character
group is finitely generated, each field-valued point selects an additive character
equivalence and a nonvanishing coefficient product. Every scalar extension making
that product invertible makes the bialgebra map exactly the corresponding map on
character degrees.

Scalar extension preserves the equivalence by the tensor-product algebra
equivalence. The field selects the character equivalence by the published
`characterEquiv` construction. The generator coefficient product and the equality
after scalar extension are the existing `DiagonalIsomorphismLocus` lemmas.

`exists_character_certificate_at_prime` applies this construction to the residue
field of any prime ideal. `characterCertificateAtPrime` chooses the additive
equivalence and the element outside that prime, retaining the identity for every
commutative algebra in the specified scalar-extension universe. The character
groups may lie in independent universes. Only finite generation of the source as
an additive monoid is required; finiteness of either character group is not a
hypothesis.

This is the algebraic locality certificate. Transport to group-scheme
automorphisms and arbitrary scheme tests is separate.
