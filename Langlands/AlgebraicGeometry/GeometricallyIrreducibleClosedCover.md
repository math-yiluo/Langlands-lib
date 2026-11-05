# Components of finite geometrically irreducible closed covers

This internal unit derives a component comparison from the elementary finite
closed-cover characterization of irreducibility and the published equal-support
comparison for geometric irreducibility.

Given a finite family of actual closed immersions with irreducible sources
whose ranges cover a scheme, every actual maximal irreducible component is
the range of one member of the family. The proof applies
`isIrreducible_iff_sUnion_isClosed` to that component and the finite set of
ranges. It obtains containment in one range; maximality of the component and
irreducibility of the range turn containment into equality.
`componentClosedCoverIndex` chooses this proved member for each component,
and `range_componentClosedCoverIndex` records its actual range equality.
The index family may be empty when the scheme is empty.

Over a field, a geometrically irreducible source is irreducible.
`componentsGeometricallyIrreducible_of_finite_closed_cover` therefore applies
the comparison to any finite geometrically irreducible closed cover. Each
actual maximal component is given the closed subscheme defined by its
vanishing ideal. That inclusion and the selected cover member have exactly
the same support, so the published equal-support theorem transfers geometric
irreducibility to the actual reduced closed component.

The scheme and field share arbitrary universe `u`; the finite index type has
an independent universe. There are no finite-type, quasi-compactness,
Noetherianity, reducedness or separation hypotheses. This unit constructs
neither a splitting field nor a finite closed cover; those remain inputs to
its comparison theorem.
