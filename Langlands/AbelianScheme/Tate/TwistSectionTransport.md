# Geometric transport on the section-ring Tate twist

The actual relative Weil pairing has values in the roots-of-unity twist over
`Γ(Spec Ω, ⊤)`. Existing geometric root transport acts on the twist over the
point field `Ω`. This internal adapter connects those types using the canonical
section isomorphism `Scheme.ΓSpecIso (.of Ω)`. It chooses no roots of unity and
does not trivialize either twist.

`Divisibility.finiteAdeleMapEquiv` bundles the existing rational twist map of a
ring equivalence as linear over the finite adeles. Its linearity uses the
existing scalar-compatibility theorem for ring-induced root maps.
`primeToFiniteAdeleMapEquiv` does the same for the orders coprime to a modulus,
with the coupled prime-to-modulus adele comparison.

`Geometry.sectionRationalEquiv s P` compares the rational twists over the
section ring of the geometric point and over its field. It is exactly the
rationalized root map of the canonical ring equivalence, retaining all orders
selected by `P`. The `sectionRationalEquiv_gm` lemma identifies this map with
the comparison already used in the affine multiplicative-group Tate module.

`sectionRationalTransport P p` first applies this comparison at the source,
then the existing geometric path transport on actual coherent roots in the
point fields, then the inverse section comparison at the target. Its
identity, composition and inverse laws follow from the corresponding field
transport laws and cancellation of the comparison equivalences.

`sectionFiniteAdeleEquiv` and `sectionFiniteAdeleTransport` bundle the same maps
over the existing finite-adele module structures. Their scalar comparison
is explicit and identical at both endpoints.
`sectionFiniteAdeleRepresentation` conjugates the actual geometric root
representation through this canonical comparison. Its multiplication laws
follow by cancellation and the existing representation laws.
`sectionFiniteAdeleTransport_aut` shows that path transport around a loop is
the resulting representation.

`sectionPrimeToFiniteAdeleEquiv`, `sectionPrimeToFiniteAdeleTransport` and
`sectionPrimeToFiniteAdeleRepresentation` give the same constructions for
the orders coprime to a modulus `m`. They use the coupled comparison `hAway`
and finite étaleness only at those retained orders. The transport has the
same underlying value as `sectionRationalTransport` for the coprime-order
selection. Its loop value is the away representation.

The assumptions for transport are those of the existing geometric root
construction: finite geometric fibres for the cover categories and finite
étaleness of the selected root-of-unity schemes over the base. This module
does not supply those theorems or assert that the Weil pairing commutes with
this transport. It provides the concrete value-module transport in which
that compatibility can be stated. The construction and its proofs are
derived entirely from the named Library comparisons and transport laws.
