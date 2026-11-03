# The semidirect group scheme of an automorphic action

This internal construction equips the actual scheme product `G × H` with the
semidirect group law associated with `AutomorphicAction H G`. On every test
scheme its group of points is the ordinary semidirect product of the groups of
points, using the given action. These coordinates commute with test morphisms.

The base scheme and universe are arbitrary. The acting group `H` need not be
commutative. The semidirect coordinates have multiplication
`(g,h) * (g',h') = (g * a.act h g', h * h')`.

`semidirectPoints` is the actual group-valued presheaf, with maps obtained by
precomposing both coordinates. The compatibility needed for these maps is
exactly the naturality law of the given scheme action. The categorical product
represents its underlying set-valued presheaf: the forward map takes the two
projections, and the inverse pairs the two morphisms.

The construction uses that representation and Mathlib's
`GrpObj.ofRepresentableBy` to put a group-object structure on the scheme
product. `semidirectPointsIso` is the induced natural group isomorphism.
`semidirectPointsEquiv` gives the same isomorphism on each test scheme, with
projection formulas and naturality proved in the file.

This is internal, derived content: it applies Mathlib's ordinary semidirect
product and representability constructions to the existing actual automorphic
action. It supplies an elementary bridge for later comparison of actions with
conjugation. This file asserts no smoothness, connectedness, Lie-image formula
or cyclic-tail comparison.
