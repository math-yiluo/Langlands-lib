# Actual models for a corrected-orbit Haar balance

This internal construction by Worker 561 supplies actual group-scheme and
finite Lie-coordinate inputs associated to a
`CorrectedOrbitCocharacterRealization r`. It uses the existing represented
subgroup constructions and makes no additional assertion about character
detection or the final rational squared-modulus target.

`torusHom` is the unique factor of the original torus inclusion through
`r.actingScheme`, the affine representative of the common full dynamic
centralizer. `Dynamic.torusFactor` constructs it because a commutative torus
centralizes each of its cocharacters. `torusHom_comp` preserves the exact
original inclusion into the ambient group.

The two radical schemes and inclusions are the published
`Dynamic.Affine.unipotentScheme` and `unipotentHom` for the two realizing
cocharacters. The published representability and closed-subgroup theorems
apply to these same inclusions on every scheme test.

`intersectionScheme` is the scheme-theoretic pullback of the two radical
inclusions. `intersectionHom` maps this pullback into the original ambient
group. The closed-subgroup intersection theorems prove that it is closed
and represents the literal infimum of the two dynamic radical functors.
The represented-subgroup point equivalence followed by
`r.intersection_points` gives `intersectionPointEquiv`, whose ambient value
is exactly `r.intersectionHom`. Its codomain is the existing literal
`CorrectedFiltration.orbitUnipotentIntersection` of the two original
standard radicals, with the target's inverse-conjugation convention.

All three inclusions are closed in an affine ambient group. They therefore
have affine sources. If the ambient group is locally of finite type over
the field, the three sources are also locally of finite type. The published
`Lie.finiteCoordinates` supplies natural coordinates over every test
algebra for each actual Lie kernel, with rank its finite dimension over
the base field. No smoothness of the intersection is assumed or needed for
this construction.

The field universe is arbitrary, and no nonempty-root, field-characteristic,
split-ambient, local-field or extra reductivity assumption is imposed.
These are model and coordinate constructions; the full Haar balance and
character-restriction injectivity remain separate proof obligations.
