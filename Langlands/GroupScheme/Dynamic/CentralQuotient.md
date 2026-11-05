# Central cocharacters under fpqc quotients

This derived supporting module works with actual group schemes over any base
scheme, at arbitrary universe. It does not prove the finite-field solvability
statement or supply a cocharacter-lifting theorem.

For a cocharacter `χ` of `H` and a homomorphism `q : H ⟶ Q`, the image
cocharacter is `χ ≫ q`. If the dynamic centralizer of `χ` is the full subgroup
functor, and the map `q × id` on the product with the multiplicative group is an
epimorphism, the image cocharacter also has full dynamic centralizer.

The proof uses the universal point, the identity of the underlying scheme of
`Q`. Its conjugation orbit becomes constant after precomposition by `q × id`,
by the published orbit functoriality and centrality in `H`. Cancellation of this
epimorphism makes the universal orbit constant. Naturality then gives the
constant-orbit identity on every test scheme. This argument does not require
surjectivity on groups of test-scheme points.

For a quasi-compact, flat, surjective underlying scheme map `q`, the published
`AutomorphicAction.effectiveEpi_whiskerRight` supplies the needed epimorphism on
the product. `centralQuotientPointsEquiv` identifies every group of `Q`-points
with the corresponding points of the full dynamic centralizer of `χ ≫ q`.
Both directions preserve the underlying `Q`-point, so this is an actual
multiplicative equivalence.

Finally, `central_cocharacters_of_fpqc_of_lifts` combines this transport with an
explicit lift of each cocharacter of `Q`. Its conclusion quantifies over
cocharacters over the same base as the source hypothesis. The lift hypothesis is
retained and is a separate geometric obligation for the intended unipotent
radical quotient application.

The provenance is internal and derived: the construction uses the actual
dynamic subgroup functors and orbit identities from `Dynamic.Functoriality` and
the existing product epimorphism result from `ActionDescent`; it adds no
literature assertion.
