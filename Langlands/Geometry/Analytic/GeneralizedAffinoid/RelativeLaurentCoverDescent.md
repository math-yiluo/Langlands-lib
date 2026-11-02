# Finite rational-cover descent along the Laurent Gauss section

This internal construction combines the actual relative Laurent domain,
continuous Gauss section, and finite rational-pullback constructions. It does
not use an additional literature assertion.

Let `K : Type u` be a complete ultrametric normed field, `A` an actual
finite positive-polyradius presented affinoid algebra over `K`, `t` any positive
real number, and `U : Domain K A` a full represented domain. Write `A_t` for
`RelativeLaurentAnnulus.algebra K A t` and `U_t` for
`RelativeLaurentAnnulus.liftedDomain K t U`.

The construction `finiteRationalCoverDescent` takes a
`Domain.FiniteRationalCover U_t` and returns a
`Domain.FiniteRationalCover U`. The output charts are actual rational charts
over the original ambient algebra `A`. Every chart has an actual domain arrow
to `U`, hence an actual bounded map from `U.algebra` to its rational quotient,
commuting with the maps from `A`.

For each chart upstairs, `rationalPullbackCharts` expresses its inverse image
under the actual Gauss section as a finite union of rational loci over `A`.
The theorem `exists_finite_family_rational_pullback` flattens these finite
families by enumerating the dependent sum of their finite index types.
`rationalFamilyPullbackCharts` chooses the resulting family, and
`mem_rationalFamilyPullbackCharts` records its exact pointwise equivalence.
The original finite index type may lie in a separate universe `v`.

If the upstairs chart loci lie in `U_t.locus`, the exact identity

`gaussSection K A t ⁻¹' U_t.locus = U.locus`

places every descended chart locus inside `U.locus`. Full representation of
`U` then constructs each actual bounded restriction, using
`Domain.inclusionOfSubset`; the arrows are not only subset witnesses.
For any point of `U.locus`, its Gauss-section image belongs to `U_t.locus`
and thus to some chart in the given cover. The pointwise pullback equivalence
puts the original point into a descended chart. This proves coverage.

`domainGaussSection` restricts the continuous section to these represented
loci. The construction `finiteRationalNeighborhoodDescent` uses continuity
to pull back a relative neighborhood that is a finite union of rational
loci. The same finite-family equivalence identifies this preimage with the
union of the descended charts, and the same containment argument supplies
their actual arrows. `rationalNeighborhoodDescent` specializes this to one
relative rational neighborhood upstairs. An individual member of the
descended family need not itself be a neighborhood.

All constructions retain arbitrary positive real radii, trivial valuations,
zero and nonreduced quotient algebras, empty original coordinate tuples,
empty spectra and empty domains. Empty chart families are permitted, and
there is no radius-independence or strictness hypothesis.

This is a supporting descent construction. It requires a finite cover or a
local rational neighborhood upstairs and does not construct such a cover
unconditionally, identify the annulus with an affinoid over an extension
field, prove strictification, or prove
`Domain.FiniteRationalCoverStatement`.
