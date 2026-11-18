# Actual covers retaining a selected geometric factor

This derived internal construction starts with the actual orbit Weil inclusion.
Its scalar extension is the original orbit subproduct inclusion, precomposed with
an explicit isomorphism. Faithfully flat reflection therefore proves closedness
and all-test normality of the original Weil inclusion. Smoothness and connectedness
of the actual orbit product also reflect to its original Weil source.

For a simply connected ambient group, apply the published arbitrary-field normal
complement theorem to that prescribed closed smooth connected normal subgroup.
Its product multiplication is a central isogeny; simple connectedness of the
target makes it an isomorphism. The complementary factor is simply connected,
as follows from simple connectedness of the product. Its left insertion recovers
the original actual Weil inclusion exactly.

`orbitWeilFactor` packages these data as a `SimplyConnectedWeilFactor`. The field
and extension-field group are definitionally the selected geometric factor's
exact stabilizer field and its original descended group. The ambient group
need not be almost-simple, and there is no characteristic restriction.
