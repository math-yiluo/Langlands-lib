# Common maximal split tori through a reductive special-fibre quotient

This internal derived unit isolates the maximality assertions needed by
`UnramifiedFacetCommonTorusStatement`. It does not assert the Lie-weight sign
formula or the existence of any model, quotient, torus, or building.

`CommonTorusMaximalityStatement` is the common-torus maximality implication over
any noetherian Henselian domain with perfect residue field and fraction field.
It uses a connected reductive generic group, a compatible morphism between
supplied relative-component models, a reductive special-fibre quotient of the
target, and supplied integral torus data for a maximal split generic torus.
The source torus clause is assumed. The conclusion `HasMaximalSplitTori` means
that the same special-fibre torus is maximal split in the source, target, and
target quotient, with the actual inclusions defined in `SpecialFibre`.

The proof `commonTorusMaximality` retains source maximality from the given torus
clause. It obtains target maximality from the published Henselian specialization
argument in `CommonTorusMaximality`. The quotient helper
`RelativeComponentModelHom.isMaximalSplitTorus_quotientTorusInclusion` applies the
published perfect-field unipotent-kernel maximality equivalence to the supplied
radical inclusion and quotient projection. The reductive-quotient predicate
provides the radical's closedness, smoothness, connectedness and unipotence, the
represented fppf quotient, and smoothness of the reductive quotient. Affineness
and finite type of the neutral special fibre come from base change of its
integral model. Smoothness supplies finite type locally for the quotient. Thus
this helper preserves the original torus source, including closed immersion
into the quotient; it does not merely compare split ranks or rational points.

`RelativeComponentModelHom.hasMaximalSplitTori_integer` specializes this result
to the integers of a nonarchimedean local field and the conjugate of the maximal
split torus carried by supplied `ParahoricBuildingData`. The valuation ring is
noetherian and Henselian and its finite residue field is perfect. Generic
maximality is transported by the inner automorphism. The result requires no
facet incidence, apartment descent, or characterization of integral points.

All content is derived from the existing Library interfaces and results cited
above. KP Axiom 4.1.22(3) motivates the consumer, but this unit proves only the
maximality assertions; the actual schematic-image Lie-weight computation
remains a separate obligation.
