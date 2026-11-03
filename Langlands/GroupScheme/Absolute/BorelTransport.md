# Borel subgroup presentations and conjugated containment

Worker 1293.

This module derives elementary transport lemmas from the published definitions
of `IsSolvableGroupScheme` and `IsBorelSubgroup`. The base field is arbitrary,
of arbitrary characteristic and universe. No Borel existence or conjugacy
theorem is assumed or established here.

The provenance is internal: functoriality of base change, group isomorphisms on
all test points, isomorphism invariance of smoothness and connectedness, the
published subgroup representation API, and the maximality field in the
definition of a Borel subgroup suffice.

`IsSolvableGroupScheme.of_iso` base changes an actual group-scheme isomorphism
to the algebraic closure and applies its point-group isomorphism. Solvability
transfers along the resulting injective homomorphism.

`IsBorelSubgroup.iso_comp` changes the source presentation. Closedness,
smoothness, connectedness and solvability transfer along the source
isomorphism. A factorization from the new source gives one from the old source
by precomposing with the inverse; maximality makes that composite, and hence
the original factorization, an isomorphism.

`IsBorelSubgroup.comp_iso` changes the ambient group by any isomorphism,
including an actual inner automorphism. Pull a competing closed subgroup
back along the inverse isomorphism and apply the original maximality.

`IsBorelSubgroup.of_range_eq` and `isBorelSubgroup_iff_of_range_eq` show that
two closed embeddings with the same subgroup functor on every test scheme
have the same Borel property. The published representation API gives an actual
isomorphism of the sources commuting with the embeddings, and `iso_comp`
transports the property. Equality on rational points alone is not used.

Finally, `IsBorelSubgroup.conjugatingIsoOfFactor` takes two existing
Borel embeddings and an actual factorization
`f ≫ i' = i ≫ (G.innerIso g).hom`. The preceding ambient transport and
maximality prove that `f` is an isomorphism. Its `asIso` is the isomorphism
required by the equation in `BorelConjugacyStatement`. The constructed
isomorphism has underlying homomorphism exactly `f`, and
`conjugatingIsoOfFactor_hom_comp` proves its embedding equation.
`IsBorelSubgroup.exists_conjugatingIso_of_factor` packages this construction
as an existence theorem. The geometric existence of such a point and
factorization remains a separate obligation.
