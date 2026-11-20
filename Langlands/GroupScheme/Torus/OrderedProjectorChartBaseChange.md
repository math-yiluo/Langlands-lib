# Base change of the ordered projector charts

The pullback adjunctions for the source and target identify points of an iterated pullback with points of the original group on the same underlying test scheme. `baseTestComparison` is the identity on the common underlying test scheme. The point comparison preserves the projection to the original group. In the diagonalizable and general linear point models, the character and matrix values consequently agree.

`pullHom_subgroupHom` uses this comparison on both sides of the weighted matrix formula. Composition of the global function maps gives the projector entries on the new base. The result is the actual subgroup homomorphism of the pulled-back projectors.

`evaluate_chartFamily` applies the comparison to the universal projector family. By naturality of the ordered projector scheme's point equivalence, its pullback is exactly the family corresponding to the chosen chart point. `evaluate_comp_chartMap` then identifies the subgroup at the composite parameter in the universal moduli with this explicit projector subgroup. This is an internal compatibility for comparing charts on common tests.
