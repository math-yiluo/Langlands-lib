# Integrality of tori over fields

This internal helper derives integrality from the published definitions of
`IsSplitTorus` and `IsTorus`. It adds no structural premise about the ground field.

For a split torus, the implemented proof uses its published isomorphism with the
spectrum of the Laurent group algebra of a finite free abelian group. This algebra
is a domain over a field. For a general torus, the defining splitting field
extension gives an integral base change. Its projection onto the original torus is
surjective and scheme-theoretically dominant. Irreducibility descends by
surjectivity, and reducedness descends by injectivity on sections. Mathlib then
combines irreducibility and reducedness to obtain integrality.

These are derived scheme-theoretic consequences of the existing torus
definitions and the Laurent presentation, rather than a separately assumed
literature theorem.
