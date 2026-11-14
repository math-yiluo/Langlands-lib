# Exact Henselian lifting from a split torus

This internal supporting result concerns a Henselian local ring `R`, a field
`k` with a surjective structural map from `R`, an actual split torus `H` over
`R`, and a smooth affine group scheme `G` over `R`. Every group-scheme
homomorphism from `H_k` to `G_k` is the base change of a homomorphism from `H`
to `G`. The reduction is exactly the prescribed homomorphism. There is no
uniqueness claim.

The cocharacter specialization uses the canonical `Gm.baseChangeIso` to state
that every cocharacter of `G_k` lifts exactly to a cocharacter of `G`. These
are homomorphisms of group schemes, so their equalities hold on every scheme
test.

The implementation uses the published smooth representability of the actual
relative Hom functor from a split torus. A prescribed residue homomorphism
has a parameter in that smooth scheme. The published Henselian section
theorem lifts that parameter through its prescribed residue point.
Functoriality of evaluation gives the exact reduction. The identity
pullbacks in the relative Hom functor are removed by `baseChangeIdIso`;
`evaluate_identityBase` checks that this removal agrees with actual base
change by comparing the scheme pullback projections.

`HenselianSplitSourceLiftingStatement` is the Prop-valued statement of the
general lifting assertion, proved by `henselianSplitSourceLifting`. All
declarations are at arbitrary universe `u`. This is derived from the
published Hom-scheme and Henselian-section interfaces, with no new claim
about the translation of original literature.

For the incident-facet parabolic problem, the result supplies an exact
integral lift once a residue cocharacter in the neutral special fibre is
specified. It does not construct facet models, identify their images with
parabolics, or prove the facet-to-parabolic bijection.
