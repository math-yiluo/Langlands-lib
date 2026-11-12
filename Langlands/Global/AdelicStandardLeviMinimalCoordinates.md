# Actual minimal-parabolic coordinates inside a canonical standard Levi

This internal derived unit constructs the group-scheme morphism and the adelic
factor comparison needed to apply root-Levi height arguments to original
minimal-parabolic coordinates. The index `J` is any subset of the actual simple
relative roots of the supplied maximal split torus and generic cocharacter of
a connected reductive group over a number field. No split-group hypothesis is
imposed.

`Standard.minimalLeviToLevi` is the actual group-scheme morphism from the
original canonical minimal Levi to the canonical standard Levi indexed by `J`.
The published standard-parabolic order gives the inclusion of their subgroup
functors, and the published represented-subgroup construction turns that
inclusion into the morphism. Its composite with the standard Levi inclusion is
exactly the original minimal Levi inclusion.

`exists_standardLevi_minimal_unipotent_factors` splits every actual adelic point
of the original minimal unipotent into an intrinsic minimal-unipotent point of
the standard Levi followed by an outer standard-unipotent point. The proof
evaluates the published all-test equality
`U_empty = (L_J intersect U_empty) U_J` on the full adele test algebra.
Representability lifts the intersection factor into the canonical standard
Levi. The published standard-family intersection comparison identifies its
membership with the intrinsic empty-index unipotent subgroup in that Levi.
Representability then supplies actual points of both unipotent source schemes,
and their original ambient images have the asserted ordered product.

`exists_standardLevi_minimal_coordinates` applies this split to a supplied
ordered minimal-Levi, torus, unipotent product. It maps the original intrinsic
norm-one minimal-Levi point along `minimalLeviToLevi` using `mapNormOne`, and
uses the actual torus lift into the same canonical standard Levi. Their
product with the intrinsic unipotent point gives a raw standard-Levi factor,
followed by the outer unipotent. The raw factor has no asserted intrinsic
norm-one membership. Its torus point is exactly the originally supplied point.
Functoriality of the actual adelic maps and the two composite identities prove
the equality.

The provenance is the published standard-parabolic order, realizing standard
cocharacters, all-test unipotent product, canonical standard-family intersection
comparison, represented subgroup functors and norm-one functoriality. This unit
does not assume or prove arithmetic height bounds, construct original positive
minimal-parabolic coordinates, or conclude chamber reduction.
