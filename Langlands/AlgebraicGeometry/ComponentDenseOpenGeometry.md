# Generic-point open reduction for geometric component properties

Internal infrastructure for the arbitrary, possibly non-quasi-compact scheme case
of finite separable component splitting.

`exists_isCompact_open_containing_genericPoints` chooses one affine neighbourhood
of each generic point and takes their union. A scheme with finitely many maximal
irreducible components has finitely many generic points, so the union is
quasi-compact. No separatedness or Noetherian hypothesis is used.
`genericPointCompactOpen` chooses one such open and packages its compactness
and the containment of all generic points in a subtype.

`geometricallyIrreducible_of_dense_open` proves that a geometrically irreducible
dense open subscheme of a scheme over a field makes the whole scheme
geometrically irreducible. After any extension of the base field, the inverse
image of the open is dense because the scalar-extension projection is open.
The pullback of the open subscheme is irreducible by its assumed geometric
irreducibility, so the closure of its image is the whole scalar extension and is
irreducible.

`ComponentsGeometricallyIrreducible.of_open_containing_genericPoints` recovers
geometric irreducibility of every actual reduced component of the ambient
field-scheme from that property on an open containing all its generic points.
For each ambient component, its intersection with the open is a component of
the open. Pull back the ambient component's actual vanishing-ideal immersion
to the open. Its support equals that open component, so the published
closed-support invariance theorem gives geometric irreducibility of this
pullback. The comparison uses only equality of supports; the pullback here
is also reduced because it is an open subscheme of the reduced component.
Its image in the ambient component is a nonempty open, hence dense, and the preceding
dense-open theorem finishes the argument.

`genericPoints_subset_preimage_of_flat` proves that the preimage of a
generic-point neighbourhood under any flat scheme morphism again contains all
generic points. It applies the published generic-point preservation theorem to
the generalizing map underlying a flat morphism. This result requires no field
hypothesis.

These constructions and lemmas are derived internally from Mathlib's affine
neighbourhood, sobriety, open scalar extension, and topological irreducibility
APIs, together with the published closed-support geometric irreducibility
comparison and generic-point preservation lemmas. Every field and scheme lies
in the same arbitrary universe. They do not construct a finite separable
extension or descend component ideals; those remain separate obligations of
finite separable component splitting.
