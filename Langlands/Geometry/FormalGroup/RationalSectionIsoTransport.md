# Integral-isomorphism transport of invertible rational sections

This internal construction combines actual rational-section composition with
the existing integral-isomorphism transport. It supplies transport of an
existing pair of mutually inverse sections. It attributes no theorem to the
original literature.

Let `O` be a commutative ring, `R` a commutative `O`-algebra and `F` an
`O`-algebra field. The ring `R` and field `F` share a universe. All coordinate
types are finite and may differ. No domain, fraction-field, nilpotence or
isogeny hypothesis is needed.

For integral isomorphisms `a : M ≅ M'` and `b : N ≅ N'`, the existing
section transport sends `z` to `b ∘ z ∘ a⁻¹`, using the actual integral
maps as sections. The new `RationalSection.transportIso_id` and
`transportIso_comp` prove preservation of identity and composition. The
proofs use associativity of section composition and cancel the actual
integral inverse maps at the common endpoint.

`RationalSectionIso.transportIso` applies this operation to the forward
section of an existing section isomorphism, and applies the reversed pair
of integral comparisons to its reverse section. Preservation of composition
and identity proves both inverse equations. The forward and reverse formulas
are definitional.

The module proves compatibility with restriction to every smaller open,
identity section isomorphisms, reversal and composition. Transport by the
inverse pair of integral isomorphisms returns the original section isomorphism.
`transportIsoEquiv` packages these operations as an actual equivalence. Equality
of the objects follows from the existing forward-section extensionality,
which itself uses uniqueness of the actual two-sided inverse.

This construction supplies no inverse-existence theorem for arbitrary local
quasi-isogenies. It transports inverses already contained in a
`RationalSectionIso`; it does not identify that type with the local
scalar-isogeny condition.
