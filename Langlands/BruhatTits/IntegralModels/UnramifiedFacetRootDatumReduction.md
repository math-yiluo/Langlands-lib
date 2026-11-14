# The descended facet root datum from integral opposite factors

This internal assembly works at arbitrary universe `u`. It combines
`UnramifiedFacetQuotientRoots` with `UnramifiedFacetRootDatumAssembly`.
The only global proposition left as a premise is
`IntegralOppositeFactorsStatement`. This unit does not prove that premise.

For supplied data, `P` is a parahoric building datum over a nonarchimedean local
field with affine ambient group, apartment axioms and root reflections. The
comparison `e` with a maximal-unramified building is injective and equivariant.
The neutral model's integral points after maximal-unramified base change are
exactly the intersection of the specified zero subgroup with the pointwise
fixer of the image of `g`'s translated nonempty apartment subset `Fa`.
The supplied integral torus `T` is closed and split and has generic inclusion
`P.i` followed by the actual inner automorphism associated to `g`. `Q` is the
actual reductive quotient of the neutral special fibre, and `Droot` is arbitrary
relative-root reflection data for `P.i`.

The entry definition `unramifiedFacetRootDatumOfIntegralOppositeFactors` constructs
a root datum on the actual quotient-root subtype and actual special-torus
character and cocharacter lattices. It satisfies `IsRootDatumOf` for the actual
quotient-torus inclusion, and its entire graph of root-coroot pairs equals
`apartmentDerivativeRootCorootGraph` for `Fa`, using canonical specialization
through the same integral torus. The exact root comparison is proved by the
imported equivalence for ordinary affine derivatives. The imported assembly
constructs actual quotient reflection representatives with the full prescribed
character reflection formula, which identifies the specialized coroots.

`hasApartmentDerivativeRootDatum_of_integralOppositeFactors` packages this
construction into the existing `HasApartmentDerivativeRootDatum` predicate,
including finiteness of the actual quotient-root subtype. It works for every
proof of splitness of the supplied integral torus.

`unramifiedFacetRootDatum_of_integralOppositeFactors` proves the full existing
`UnramifiedFacetRootDatumStatement` with this sole additional global premise.
It introduces all seven building hypotheses, all eight apartment-descent
hypotheses, and every supplied datum and model-characterization hypothesis of
the unchanged statement. The translated-facet equality rewrites the model
characterization to the form used above. The apartment-facet witness supplies
a point, hence nonemptiness of `Fa`. The first component of `SatisfiesTorusClause`
gives closedness and splitness. Applying the supplied-data theorem proves the
required predicate for the arbitrary quotient, torus, reflection datum and
splitness witness. Several hypotheses of the full statement are stronger than
those needed by this composition and remain quantified exactly as published.

This is an internal composition of the named supporting results, with no new
original-literature formulation. The host proof without additional premises
remains open until the integral opposite-factor statement is independently
proved. The published host statement and its import closure are unchanged.
