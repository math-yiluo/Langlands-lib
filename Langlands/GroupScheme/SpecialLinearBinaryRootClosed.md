# Closed additive root subgroups of the binary special linear scheme

This internal construction continues the explicit additive root maps of
`SpecialLinearBinaryRootGroups`. Over every commutative base ring, the
transvection range is cut out by requiring each entry outside its root position
to equal the corresponding identity entry. The quotient by these equations
provides a closed subgroup scheme. The sole additive coordinate gives a natural
equivalence on all relative test schemes, hence an isomorphism of this closed
representative with the actual additive group. Its composite with the closed
inclusion is the previously constructed root map.

`isClosedSubgroup_rootMap` proves that the actual root map is a closed immersion.
`mem_range_rootMap` identifies its points on every relative test scheme by the
complementary entry equations. This construction uses the published ideal-cut
subgroup machinery and explicit matrix formulas; it invokes no classification
or arithmetic result.

This module does not prove that the subgroup is a geometric unipotent radical,
that its ambient triangular subgroup is parabolic, or that general local
Kneser–Tits holds.
